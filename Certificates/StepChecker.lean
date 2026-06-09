/-
  StepChecker.lean

  Arithmetic checker for one linear-combination reduction step.

  Uses the decoded types from `JsonDecode` directly:
    `LinearCombination`, `LCTerm`, `Coefficient`,
    `ReplacementCertificate`, `Step`, `Certificate`.

  The check performed for each step:

    expectedAfter
      = (before.terms with selected term removed)
        ++ [ (selectedCoeff × rc.coefficient, rc.afterGraph)
             | rc ∈ step.replacementCertificates ]

    normalize expectedAfter  =?=  normalize step.after

  "Normalize" means: parse each `Coefficient` to `Poly`, drop trailing
  zeros, drop zero-coefficient terms.  Comparison is structural /
  position-by-position; no multiset reordering.

  Graph-level validity (`Replacement.valid`) is a separate concern and
  is not checked here.
-/

import Certificates.Polynomial
import Certificates.JsonDecode

open Polynomial

namespace StepChecker

-- ─── Coefficient parsing ─────────────────────────────────────────────────────

/-- Parse a single coefficient string ("3", "-2", "1/2", "-3/4") to `Rat`. -/
private def parseRat (s : String) : Except String Rat :=
  let t := s.trimAscii.toString
  match t.splitOn "/" with
  | [n] =>
    match n.trimAscii.toString.toInt? with
    | some i => .ok (i : Rat)
    | none   => .error s!"cannot parse '{s}' as integer"
  | [n, d] =>
    match n.trimAscii.toString.toInt?, d.trimAscii.toString.toInt? with
    | some num, some den =>
      if den = 0 then .error s!"zero denominator in '{s}'"
      else .ok ((num : Rat) / (den : Rat))
    | _, _ => .error s!"cannot parse '{s}' as rational"
  | _ => .error s!"malformed rational '{s}'"

/-- Parse a `Coefficient` (array of strings) into a normalized `Poly`. -/
private def parseCoeff (c : Coefficient) : Except String Poly := do
  let rats ← c.coefficients.toList.mapM parseRat
  return Polynomial.normalize rats

-- ─── Graph equality ──────────────────────────────────────────────────────────

/-- Structural equality on `RawClosedGraph` (all four parallel arrays). -/
private def graphEq (g1 g2 : RawClosedGraph) : Bool :=
  g1.darts    == g2.darts    &&
  g1.vertices == g2.vertices &&
  g1.vertexOf == g2.vertexOf &&
  g1.partner  == g2.partner

-- ─── Array helper ────────────────────────────────────────────────────────────

/-- Remove the element at index `i`, returning it paired with the remainder.
    Returns `none` if `i` is out of range. -/
private def removeAt (arr : Array α) (i : Nat) : Option (α × Array α) :=
  match arr[i]? with
  | none   => none
  | some x => some (x, arr.extract 0 i ++ arr.extract (i + 1) arr.size)

-- ─── Term normalization ───────────────────────────────────────────────────────

/-- Parse one `LCTerm` to `(Poly, RawClosedGraph)` with a normalized coefficient. -/
private def parseTerm (t : LCTerm) : Except String (Poly × RawClosedGraph) := do
  let p ← parseCoeff t.coefficient
  return (p, t.graph)

/-- Parse an array of `LCTerm`s, dropping any whose coefficient is zero. -/
private def parseTerms (ts : Array LCTerm)
    : Except String (Array (Poly × RawClosedGraph)) := do
  let parsed ← ts.mapM parseTerm
  return parsed.filter fun (p, _) => !p.isEmpty

-- ─── Step checker ────────────────────────────────────────────────────────────

/-- Check one reduction step.

    Constructs `expectedAfter`:
    1. Parse `before.terms`, removing the term at `step.termIndex`.
    2. For each `rc` in `step.replacementCertificates`, compute
         coeff = normalize (selectedCoeff × rc.coefficient)
         graph = rc.afterGraph
       and append those terms.
    3. Drop zero-coefficient terms.

    Then parse and normalize `step.after`, and compare the two arrays
    position-by-position (coefficient via `Polynomial.beq`, graph
    structurally). -/
def checkStep (before : LinearCombination) (step : Step) : Except String Unit := do
  -- (1) Extract selected term and remaining terms.
  let (selected, remaining) ←
    match removeAt before.terms step.termIndex with
    | none      => throw s!"term_index {step.termIndex} out of range \
                            (before has {before.terms.size} terms)"
    | some pair => pure pair
  -- (2) Parse selected term's coefficient.
  let selectedCoeff ← parseCoeff selected.coefficient
  -- (3) Build replacement terms.
  let newTerms ← step.replacementCertificates.mapM fun rc => do
    let rcCoeff ← parseCoeff rc.coefficient
    let prod    := Polynomial.normalize (Polynomial.mul selectedCoeff rcCoeff)
    return (prod, rc.afterGraph)
  -- (4) Assemble and normalize expected after.
  let remainingParsed ← remaining.mapM parseTerm
  let allTerms         := remainingParsed ++ newTerms
  let expected         := allTerms.filter fun (p, _) => !p.isEmpty
  -- (5) Parse and normalize step.after.
  let actual ← parseTerms step.after.terms
  -- (6) Position-by-position comparison.
  if expected.size ≠ actual.size then
    throw s!"after size mismatch: expected {expected.size} terms, \
             got {actual.size}"
  for i in List.range expected.size do
    match expected[i]?, actual[i]? with
    | some (ep, eg), some (ap, ag) =>
      if !Polynomial.beq ep ap then
        throw s!"term {i}: coefficient mismatch"
      if !graphEq eg ag then
        throw s!"term {i}: graph mismatch"
    | _, _ => throw s!"internal error: index {i} out of range"

/-- Check every step in sequence, threading `after` as the new `before`.
    Returns the final `LinearCombination` on success, or the first error. -/
def checkAllSteps (cert : Certificate) : Except String LinearCombination :=
  cert.steps.foldlM (fun before step => do
    checkStep before step
    return step.after) cert.initial

end StepChecker
