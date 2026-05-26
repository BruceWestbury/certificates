/-!
# Certified reductions of trivalent graph linear combinations

This file introduces the algebraic certificate layer for checked reduction
steps in linear combinations of trivalent graphs.

**Design principles**:
* Lean checks supplied bookkeeping certificates; Python discovers reductions.
* Linear combinations use `Finsupp` directly.
* The layer is purely declarative — no rewriting, no search automation.

`Main` is imported transitively, bringing in `Mathlib` together with
`ClosedGraph`, `OpenGraph`, `Occurrence`, and the parameterised `Replacement`.
-/

import Main

-- ============================================================
-- Linear combinations
-- ============================================================

/-- A finitely supported linear combination.

    `LC R Graph` is an alias for `Graph →₀ R`: a finitely supported function
    from graph labels to coefficients.  The coefficient ring `R` is listed
    first so that `LC R Graph` reads as "linear combination over `R` indexed
    by `Graph`". -/
abbrev LC (R : Type) (α : Type) [Zero R] := α →₀ R

-- ============================================================
-- Single linear substitution step
-- ============================================================

/-- Certificate for one term-substitution step in a linear combination.

    The step isolates the contribution `Finsupp.single chosen coeff` from
    `before` and replaces it by `coeff • replacement`, while leaving the
    remaining terms `rest` unchanged.

    The two proof fields `before_ok` and `after_ok` are the bookkeeping
    identities that Lean verifies:

    ```
    before  =  Finsupp.single chosen coeff + rest
    after   =  coeff • replacement + rest
    ```
-/
structure LinearSubstitutionCert
    (R : Type) [Semiring R]
    (Graph : Type) [DecidableEq Graph] where
  /-- The linear combination before the substitution step. -/
  before      : LC R Graph
  /-- The linear combination after the substitution step. -/
  after       : LC R Graph
  /-- The graph whose term is being substituted. -/
  chosen      : Graph
  /-- The coefficient of `chosen` in `before`. -/
  coeff       : R
  /-- All remaining terms, unchanged by this step. -/
  rest        : LC R Graph
  /-- The replacement linear combination (before scaling by `coeff`). -/
  replacement : LC R Graph
  /-- Proof that `before` decomposes into the isolated term plus the residual. -/
  before_ok   : before = Finsupp.single chosen coeff + rest
  /-- Proof that `after` is the scaled replacement plus the residual. -/
  after_ok    : after  = coeff • replacement + rest

namespace LinearSubstitutionCert

variable {R : Type} [Semiring R] {Graph : Type} [DecidableEq Graph]

/-- Reading off `before` at the chosen graph yields `coeff + rest chosen`.

    This is an immediate pointwise consequence of `before_ok`:
    `Finsupp.single chosen coeff` evaluates to `coeff` at `chosen`, and
    the `Finsupp` addition is pointwise. -/
lemma before_chosen_eq (c : LinearSubstitutionCert R Graph) :
    c.before c.chosen = c.coeff + c.rest c.chosen := by
  simp [c.before_ok]

/-- Reading off `after` at any graph `g` yields `coeff • replacement g + rest g`.

    This is an immediate pointwise consequence of `after_ok`:
    scalar multiplication and `Finsupp` addition are both pointwise. -/
lemma after_apply_eq (c : LinearSubstitutionCert R Graph) (g : Graph) :
    c.after g = c.coeff • c.replacement g + c.rest g := by
  simp [c.after_ok]

end LinearSubstitutionCert

-- ============================================================
-- Higher-level reduction step
-- ============================================================

/-- A single certified reduction step in a linear combination.

    Bundles two certificates:

    * **`combCert`**: a `Replacement L Pat G H occ` asserting that the
      local graph substitution `L ↦ Pat` within closed host `G` is valid
      (complement isomorphism with ordered boundary compatibility).

    * **`algStep`**: a `LinearSubstitutionCert R Graph` asserting that
      the corresponding update to the linear combination is arithmetically
      correct.

    The abstract `Graph` label type used in the linear combination is
    separate from `ClosedGraph`; in practice it carries canonical
    identifiers produced by the external Python layer.  Lean does not
    require it to be `ClosedGraph`. -/
structure ReductionStep
    (R     : Type) [Semiring R]
    (Graph : Type) [DecidableEq Graph]
    (L Pat : OpenGraph)
    (G H   : ClosedGraph)
    (occ   : Occurrence L G) where
  /-- Combinatorial certificate: the valid graph-level occurrence replacement. -/
  combCert : Replacement L Pat G H occ
  /-- Algebraic certificate: the correct linear-combination bookkeeping. -/
  algStep  : LinearSubstitutionCert R Graph
