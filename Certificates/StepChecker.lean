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

-- ─── Graph equality ──────────────────────────────────────────────

/--
Elementwise equality for arrays of natural numbers.

Although Lean provides `BEq (Array Nat)`, the checker previously observed
failures when graph equality was implemented using `==` on arrays.
Since graph equality is a trusted part of certificate validation, we
avoid the typeclass instance and compare entries explicitly using
`Nat.decEq`.

If this function is replaced by `==`, rerun the certificate test suite
before trusting the result.
-/
private def arrayNatEq (a b : Array Nat) : Bool :=
  a.size == b.size &&
  Id.run do
    for i in List.range a.size do
      if a[i]! != b[i]! then return false
    return true

/-- Structural equality on `RawClosedGraph`.
    `darts` and `vertices` are both ranges `0..n-1`; equal size ⟺ equal array.
    `vertexOf` and `partner` are compared element-by-element via `arrayNatEq`. -/
private def graphEq (g1 g2 : RawClosedGraph) : Bool :=
  g1.darts.size    == g2.darts.size    &&
  g1.vertices.size == g2.vertices.size &&
  arrayNatEq g1.vertexOf g2.vertexOf   &&
  arrayNatEq g1.partner  g2.partner

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

/-- Merge `(p, g)` into an accumulator list.
    Uses `List` throughout to avoid `Array.set!` copy-on-write aliasing. -/
private def mergeIntoList
    (acc : List (Poly × RawClosedGraph))
    (p   : Poly)
    (g   : RawClosedGraph)
    : List (Poly × RawClosedGraph) :=
  if p.isEmpty then acc
  else
    let rec go : List (Poly × RawClosedGraph)
                → List (Poly × RawClosedGraph)  -- reversed prefix seen so far
                → List (Poly × RawClosedGraph)
      | [],            rev => (p, g) :: rev            |>.reverse
      | (q, h) :: rest, rev =>
          if graphEq g h
          then (rev.reverse) ++ [(Polynomial.normalize (Polynomial.add q p), h)] ++ rest
          else go rest ((q, h) :: rev)
    go acc []

/--
Uses a `List` accumulator rather than mutating an `Array`.

An earlier implementation used `Array.set!` while merging terms.
This produced incorrect results during certificate checking due to
interaction with Lean's copy-on-write arrays. Since normalization is
not performance critical, a purely functional implementation is used.
-/
private def normalizeTerms (xs : Array (Poly × RawClosedGraph)) :
    Array (Poly × RawClosedGraph) :=
  let lst := xs.foldl (fun acc (p, g) => mergeIntoList acc p g) []
  (lst.filter fun (p, _) => !p.isEmpty).toArray

/-- Find the index of the first term in `terms` whose graph equals `target`. -/
private def findTermByGraph (target : RawClosedGraph) (terms : Array LCTerm)
    : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if i < terms.size then
      match terms[i]? with
      | some t => if graphEq t.graph target then some i else go (i + 1)
      | none   => none
    else none
  go 0

def checkStep (before : LinearCombination) (step : Step) : Except String Unit := do
  -- (5) Parse step.after BEFORE touching the rc graphs (avoids COW aliasing).
  let parsedActual ← parseTerms step.after.terms
  -- (1) Identify and extract the selected term.
  --   `term_index` is an index into before.terms sorted by canonical graph key,
  --   not by array position.  Identify the selected term via rc[0].beforeGraph
  --   when available (exact match under `graphEq`); fall back to direct index
  --   for zero-rc steps.
  let selIdx ←
    if let some rc0 := step.replacementCertificates[0]? then
      match findTermByGraph rc0.beforeGraph before.terms with
      | some i => pure i
      | none   => throw s!"rc[0].beforeGraph not found in before.terms \
                           (step {step.termIndex})"
    else
      -- Zero-rc step: the selected term has zero net contribution.
      -- Find it by elimination: the term present in before but absent from after.
      let afterGraphs := step.after.terms.map (fun t => t.graph)
      let idx := before.terms.toList.findIdx fun t =>
        !afterGraphs.any (fun ag => graphEq t.graph ag)
      if idx < before.terms.size then pure idx
      else
        -- All before-graphs appear in after; fall back to term_index.
        pure step.termIndex
  let (_selected, remaining) ←
    match removeAt before.terms selIdx with
    | none      => throw s!"selIdx {selIdx} out of range \
                            (before has {before.terms.size} terms)"
    | some pair => pure pair
  -- (3) Build replacement terms.
  --   V2 certificate: rc.coefficient IS the final after-term coefficient.
  let newTerms ← step.replacementCertificates.mapM fun rc => do
    let rcCoeff ← parseCoeff rc.coefficient
    return (rcCoeff, rc.afterGraph)
  -- (4) Assemble and normalize expected after.
  let remainingParsed ← remaining.mapM parseTerm
  let allTerms         := remainingParsed ++ newTerms
  let expected := normalizeTerms allTerms
  -- (5 cont.) Normalize the already-parsed actual terms.
  let actual := normalizeTerms parsedActual
  -- (6) Order independent comparison.
  if expected.size ≠ actual.size then
    throw s!"after size mismatch: expected {expected.size} terms, got {actual.size}"

  -- Search manually to avoid any Array.find? argument-order ambiguity.
  let findInActual (eg : RawClosedGraph) : Option Poly :=
    actual.foldl (fun acc (ap, ag) =>
      match acc with
      | some _ => acc
      | none   => if graphEq eg ag then some ap else none) none

  let findInExpected (ag : RawClosedGraph) : Option Poly :=
    expected.foldl (fun acc (ep, eg) =>
      match acc with
      | some _ => acc
      | none   => if graphEq eg ag then some ep else none) none

  for (ep, eg) in expected do
    match findInActual eg with
    | none =>
        throw s!"expected graph missing in actual after; \
                 coeff={ep} darts={eg.darts.size} vtx={eg.vertices.size}"
    | some ap =>
        if !Polynomial.beq ep ap then
          throw s!"coefficient mismatch for matching graph; \
                   expected={ep} actual={ap}"

  for (ap, ag) in actual do
    match findInExpected ag with
    | none =>
        throw s!"actual graph not present in expected after; coeff={ap}"
    | some ep =>
        if !Polynomial.beq ep ap then
          throw s!"coefficient mismatch for matching graph; \
                   expected={ep} actual={ap}"

  pure ()

/-- Check every step in sequence, threading `after` as the new `before`.
    Returns the final `LinearCombination` on success, or the first error. -/
def checkAllSteps (cert : Certificate) : Except String LinearCombination :=
  cert.steps.foldlM (fun before step => do
    checkStep before step
    return step.after) cert.initial

end StepChecker
