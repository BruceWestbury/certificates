/-
  Polynomial.lean

  Univariate polynomials in the variable `n` with rational coefficients,
  represented as coefficient lists in ascending degree order:

    [a₀, a₁, …, aₖ]  ≙  a₀ + a₁·n + … + aₖ·nᵏ

  The empty list represents the zero polynomial.

  Only executable operations are provided; no ring-law proofs.
-/

import Mathlib.Data.Rat.Defs

namespace Polynomial

/-- A polynomial is a list of integer coefficients, lowest degree first.
    There is no canonical-form invariant on the type itself; use `normalize`
    before comparing. -/
abbrev Poly := List Rat

/-! ## Normalization -/

/-- Drop trailing zero coefficients so that the leading coefficient is
    non-zero (or the list is empty for the zero polynomial). -/
def normalize : Poly → Poly
  | [] => []
  | p  =>
    -- Reverse, drop leading zeros, reverse back.
    let trimmed := p.reverse.dropWhile (· == 0) |>.reverse
    trimmed

/-! ## Basic constructors -/

def zero : Poly := []

def one : Poly := [1]

def ofRat (a : Rat) : Poly := normalize [a]

/-- The polynomial `n`. -/
def var : Poly := [0, 1]

/-! ## Arithmetic -/

/-- Pad the shorter list with zeros so both have the same length. -/
private def padTo (n : Nat) (p : Poly) : Poly :=
  p ++ List.replicate (n - p.length) 0

/-- Pointwise addition. -/
def add (p q : Poly) : Poly :=
  let len := max p.length q.length
  let p' := padTo len p
  let q' := padTo len q
  List.zipWith (· + ·) p' q'

/-- Pointwise negation. -/
def neg (p : Poly) : Poly :=
  p.map (- ·)

/-- Pointwise subtraction. -/
def sub (p q : Poly) : Poly :=
  add p (neg q)

/-- Multiply by a scalar. -/
def smul (a : Rat) (p : Poly) : Poly :=
  p.map (a * ·)

/-- Shift coefficients up by `k` degrees (multiply by `nᵏ`). -/
private def shiftUp (k : Nat) (p : Poly) : Poly :=
  List.replicate k 0 ++ p

/-- Pair each element with its index. -/
private def indexed (l : List α) : List (Nat × α) :=
  List.zipWith (fun i x => (i, x)) (List.range l.length) l

/-- Cauchy (convolution) product. -/
def mul (p q : Poly) : Poly :=
  (indexed q).foldl (fun acc (k, c) => add acc (shiftUp k (smul c p))) zero

/-! ## Equality -/

/-- Decide equality by comparing normalized forms. -/
def beq (p q : Poly) : Bool :=
  normalize p == normalize q

-- No BEq instance: `Poly = List Rat` already has one from the standard
-- library.  Call `Polynomial.beq` explicitly for normalisation-aware
-- comparison.

/-! ## Evaluation (for testing / debugging) -/

/-- Evaluate the polynomial at a rational point. -/
def eval (p : Poly) (x : Rat) : Rat :=
  (indexed p).foldl (fun acc (k, c) => acc + c * x ^ k) 0

/-! ## Display -/

private def termStr (c : Rat) (k : Nat) : String :=
  let coefStr := toString c
  match k with
  | 0 => coefStr
  | 1 => s!"{coefStr}·n"
  | _ => s!"{coefStr}·n^{k}"

def toString (p : Poly) : String :=
  let p' := normalize p
  if p'.isEmpty then "0"
  else
    let parts := (indexed p').filterMap fun (k, c) =>
      if c == 0 then none else some (termStr c k)
    if parts.isEmpty then "0" else " + ".intercalate parts

instance : ToString Poly where
  toString := Polynomial.toString

end Polynomial

/-!  ─────────────────────────────────────────────────────────────────────────
     Linear combinations over Poly coefficients.

     A linear combination is a list of (coefficient : Poly, label : α) pairs.
     The label type α is left abstract so this layer can be reused for both
     graph terms and intermediate certificate objects.
     ─────────────────────────────────────────────────────────────────────────
-/

namespace LinearCombination

open Polynomial

/-- A single term: a polynomial coefficient and an arbitrary label. -/
structure Term (α : Type) where
  coeff : Poly
  label : α
  deriving Repr

instance [Inhabited α] : Inhabited (Term α) where
  default := { coeff := [], label := default }

/-- A linear combination is an ordered list of terms. -/
abbrev LC (α : Type) := List (Term α)

/-! ## Constructors -/

def zero : LC α := []

def singleton (c : Poly) (a : α) : LC α := [⟨c, a⟩]

/-! ## Map / filter helpers -/

def mapCoeffs (f : Poly → Poly) (lc : LC α) : LC α :=
  lc.map fun t => { t with coeff := f t.coeff }

def filterZero (lc : LC α) : LC α :=
  lc.filter fun t => normalize t.coeff != []

/-! ## Scalar operations -/

def smul (a : Poly) (lc : LC α) : LC α :=
  mapCoeffs (Polynomial.mul a) lc

def neg (lc : LC α) : LC α :=
  mapCoeffs Polynomial.neg lc

/-! ## Pointwise addition (same label structure assumed) -/

/-- Add two linear combinations term-by-term.
    Requires both lists to have the same length and labels in the same order.
    Returns `none` if the shapes differ. -/
def addAligned [DecidableEq α] (lc1 lc2 : LC α) : Option (LC α) := do
  if lc1.length != lc2.length then none
  else
    let pairs ← List.mapM id (List.zipWith (fun t1 t2 =>
      if t1.label == t2.label
      then some { coeff := add t1.coeff t2.coeff, label := t1.label }
      else none) lc1 lc2)
    some pairs

/-! ## Normalization -/

/-- Normalize every coefficient and drop zero terms. -/
def normalize [DecidableEq α] (lc : LC α) : LC α :=
  filterZero (mapCoeffs Polynomial.normalize lc)

/-! ## Equality -/

/-- Structural equality after normalization (same labels, same order). -/
def beq [DecidableEq α] [BEq α] (lc1 lc2 : LC α) : Bool :=
  let n1 := normalize lc1
  let n2 := normalize lc2
  n1.length == n2.length &&
  List.all (List.zip n1 n2) fun (t1, t2) =>
    t1.label == t2.label && Polynomial.beq t1.coeff t2.coeff

end LinearCombination
