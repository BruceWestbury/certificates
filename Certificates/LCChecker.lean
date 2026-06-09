import Certificates.JsonDecode  -- decoded certificate types
import Certificates.Graphs     -- brings in Mathlib (Rat, etc.)

/-!
# Linear-combination step checker

Verifies that `step.after` is the correct result of substituting
`before.terms[step.termIndex]` with the sequence of after-graphs
from `step.replacementCertificates`, each weighted by the product of
the before-term coefficient and the replacement-certificate coefficient.

## Scope

This module handles **only the linear-combination arithmetic**:
- coefficient polynomial multiplication
- term-count bookkeeping
- graph-identity checks (structural equality of `RawClosedGraph`)

Graph-level validity (i.e. `Replacement.valid`) is a **separate concern**
and should be called on each `ReplacementCertificate` independently.  The
call site is marked with `-- GRAPH CHECK` comments below.

## Coefficient format

Each `Coefficient.coefficients` is an array of strings representing the
coefficients of a polynomial in `n` over ℚ:
  `["a₀", "a₁", ..., "aₖ"]`  encodes  `a₀ + a₁·n + … + aₖ·nᵏ`.
Individual strings are either integers ("3", "-2") or fractions ("1/2").
-/

open Lean

-- ============================================================
-- Rational polynomial arithmetic
-- ============================================================

/-- Parse a string as a rational number.
    Accepts integers ("3", "-2") and fractions ("1/2", "-3/4"). -/
private def parseRat (s : String) : Except String Rat :=
  let t := s.trim
  let parts := t.splitOn "/"
  match parts with
  | [nStr] =>
    match nStr.trim.toInt? with
    | some n => .ok (n : Rat)
    | none   => .error s!"cannot parse '{s}' as integer"
  | [nStr, dStr] =>
    match nStr.trim.toInt?, dStr.trim.toInt? with
    | some num, some den =>
      if den = 0 then .error s!"zero denominator in '{s}'"
      else .ok ((num : Rat) / (den : Rat))
    | _, _ => .error s!"cannot parse '{s}' as rational"
  | _ => .error s!"malformed rational '{s}'"

/-- A polynomial in n with rational coefficients.
    `coeffs[i]` is the coefficient of nⁱ. -/
private structure RatPoly where
  coeffs : Array Rat

/-- Decode a `Coefficient` into a `RatPoly`. -/
private def Coefficient.toRatPoly (c : Coefficient) : Except String RatPoly := do
  let rats ← c.coefficients.mapM parseRat
  return { coeffs := rats }

/-- Polynomial multiplication by convolution. -/
private def RatPoly.mul (p q : RatPoly) : RatPoly :=
  if p.coeffs.isEmpty || q.coeffs.isEmpty then { coeffs := #[] }
  else
    let n := p.coeffs.size + q.coeffs.size - 1
    -- Use Id.run for a mutable accumulator in a pure context.
    let prod := Id.run do
      let mut r : Array Rat := Array.mkArray n 0
      for i in List.range p.coeffs.size do
        for j in List.range q.coeffs.size do
          r := r.set! (i + j) (r[i + j]! + p.coeffs[i]! * q.coeffs[j]!)
      return r
    { coeffs := prod }

/-- Remove trailing zero coefficients (normalization). -/
private def RatPoly.normalize (p : RatPoly) : RatPoly :=
  { coeffs := p.coeffs.toList.reverse.dropWhile (· == 0) |>.reverse.toArray }

/-- Polynomial equality modulo trailing zeros. -/
private def RatPoly.beq (p q : RatPoly) : Bool :=
  p.normalize.coeffs == q.normalize.coeffs

/-- Check that `c_after = c_before × c_rc` as polynomials over ℚ.
    Returns an error naming the mismatch if the check fails. -/
private def checkCoeffProduct
    (c_before c_rc c_after : Coefficient) : Except String Unit := do
  let pb ← c_before.toRatPoly
  let pr ← c_rc.toRatPoly
  let pa ← c_after.toRatPoly
  if !(pb.mul pr).beq pa then
    throw "coefficient mismatch: after-term coeff ≠ before-term coeff × rc coeff"

-- ============================================================
-- Graph and term equality
-- ============================================================

/-- Structural equality of two raw closed graphs (array-by-array comparison). -/
private def RawClosedGraph.beq (g₁ g₂ : RawClosedGraph) : Bool :=
  g₁.darts    == g₂.darts    &&
  g₁.vertices == g₂.vertices &&
  g₁.vertexOf == g₂.vertexOf &&
  g₁.partner  == g₂.partner

/-- Check that two `LCTerm`s are identical. -/
private def checkTermEq (a b : LCTerm) (label : String) : Except String Unit := do
  if a.coefficient.coefficients != b.coefficient.coefficients then
    throw s!"{label}: coefficient mismatch"
  if !a.graph.beq b.graph then
    throw s!"{label}: graph mismatch"

-- ============================================================
-- Safe array access
-- ============================================================

private def getAt {α : Type} (arr : Array α) (i : Nat) (ctx : String)
    : Except String α :=
  match arr[i]? with
  | some v => .ok v
  | none   => .error s!"{ctx}[{i}] out of range (size {arr.size})"

-- ============================================================
-- Core step checker
-- ============================================================

/-- Check one reduction step.

    `before` is the linear combination before the step.
    `step` provides `termIndex`, `replacementCertificates`, and `after`.

    Verifications:
    1. `step.termIndex` is a valid index.
    2. `step.after.terms.size = before.terms.size − 1 + replacementCertificates.size`.
    3. Unchanged **prefix**: `step.after.terms[i] = before.terms[i]`
       for `i < step.termIndex`.
    4. For each replacement certificate `rc` at offset `j`:
       (a) `step.after.terms[termIndex + j].graph = rc.afterGraph`
       (b) `step.after.terms[termIndex + j].coefficient
             = before.terms[termIndex].coefficient × rc.coefficient`
       -- GRAPH CHECK: call Replacement.valid on `rc` separately.
    5. Unchanged **suffix**: `step.after.terms[termIndex + numRc + i]
       = before.terms[termIndex + 1 + i]`.
-/
def checkReductionStep
    (before : LinearCombination)
    (step   : Step)
    : Except String Unit := do
  -- (1) term_index validity
  if step.termIndex ≥ before.terms.size then
    throw s!"term_index {step.termIndex} out of range \
             (before has {before.terms.size} terms)"
  let selectedTerm ← getAt before.terms step.termIndex "before.terms"
  -- (2) after size
  let numRc    := step.replacementCertificates.size
  let expected := before.terms.size - 1 + numRc
  if step.after.terms.size ≠ expected then
    throw s!"after has {step.after.terms.size} terms; \
             expected {expected} ({before.terms.size} − 1 + {numRc} rc)"
  -- (3) Unchanged prefix
  for i in List.range step.termIndex do
    let bt ← getAt before.terms i      "before.terms"
    let at ← getAt step.after.terms i  "after.terms (prefix)"
    checkTermEq at bt s!"prefix term {i}"
  -- (4) Replacement terms
  for j in List.range numRc do
    let rc  ← getAt step.replacementCertificates j            "replacementCertificates"
    let at  ← getAt step.after.terms (step.termIndex + j)     "after.terms (replacement)"
    -- (4a) graph identity
    if !at.graph.beq rc.afterGraph then
      throw s!"after.terms[{step.termIndex + j}].graph ≠ \
               replacementCertificates[{j}].afterGraph"
    -- (4b) coefficient product
    checkCoeffProduct selectedTerm.coefficient rc.coefficient at.coefficient
    -- GRAPH CHECK: Replacement.valid should also be called on `rc` here.
  -- (5) Unchanged suffix
  for i in List.range (before.terms.size - step.termIndex - 1) do
    let bt ← getAt before.terms (step.termIndex + 1 + i)          "before.terms (suffix)"
    let at ← getAt step.after.terms (step.termIndex + numRc + i)  "after.terms (suffix)"
    checkTermEq at bt s!"suffix term {i}"

-- ============================================================
-- Full-certificate checker
-- ============================================================

/-- Check every step in sequence, threading `after` as the new `before`.
    Returns the final linear combination, or the first error encountered. -/
def checkAllSteps (cert : Certificate) : Except String LinearCombination :=
  cert.steps.foldlM (fun before step => do
    checkReductionStep before step
    return step.after) cert.initial
