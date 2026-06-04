import Certificates.RawClosedGraph

/-!
# Validated closed dart graph — position-index layer

`ValidatedClosedGraph` is the intermediate representation between
`RawClosedGraph` (label world) and `ClosedGraph` (Fin-type world).

After `RawClosedGraph.validate` passes, every label reference is known to be
valid.  `RawClosedGraph.toValidated` materialises those references as
**positions** (plain `Nat` indices into `raw.darts` and `raw.vertices`) and
stores them in two parallel arrays:

    partnerIdx[i]  =  position of raw.partner[i]  in raw.darts
    vertexIdx[i]   =  position of raw.vertexOf[i] in raw.vertices

Both arrays have size `raw.darts.size`.  All values in `partnerIdx` are
`< raw.darts.size`; all values in `vertexIdx` are `< raw.vertices.size`.
These bounds are guaranteed by construction but not yet stated as types.

## Pipeline

    RawClosedGraph         label world  (arbitrary Nat labels)
          ↓  toValidated
    ValidatedClosedGraph   index world  (Nat positions into label arrays)
          ↓  toClosed      (future step)
    ClosedGraph            type world   (Fin n, Fin k)

Separating label→index translation from Fin proof obligations keeps each
stage simple and independently testable.
-/

-- ============================================================
-- Structure
-- ============================================================

/-- Intermediate representation after label validation.

    `partnerIdx[i]` is the position of `raw.partner[i]` in `raw.darts`.
    `vertexIdx[i]`  is the position of `raw.vertexOf[i]` in `raw.vertices`.

    Invariants (established by `toValidated`, not yet encoded as types):
    * `partnerIdx.size = raw.darts.size`
    * `vertexIdx.size  = raw.darts.size`
    * `∀ i, partnerIdx[i] < raw.darts.size`
    * `∀ i, vertexIdx[i]  < raw.vertices.size` -/
structure ValidatedClosedGraph where
  raw        : RawClosedGraph
  partnerIdx : Array Nat
  vertexIdx  : Array Nat
deriving Repr

-- ============================================================
-- Internal helper
-- ============================================================

-- `Array.indexOfNat?` in RawClosedGraph.lean is private, so we provide
-- a local copy here.  Returns the position of the first element equal to
-- `x`, or `none`.
private def findPos (arr : Array Nat) (x : Nat) : Option Nat :=
  Id.run do
    for i in List.range arr.size do
      if arr[i]! == x then return some i
    return none

-- ============================================================
-- Construction
-- ============================================================

/-- Validate `g` and, on success, build position-index arrays.

    Two-pass design:
    1. `g.validate` — checks all label-level conditions (returns on the first
       failure).
    2. Index construction — iterates over dart positions and resolves each
       label to its index using `findPos`.  The "internal" error branches are
       unreachable because `validate` already confirmed every label exists;
       they are present for exhaustiveness. -/
def RawClosedGraph.toValidated (g : RawClosedGraph) : Except String ValidatedClosedGraph := do
  -- (1) Run full structural and mathematical validation.
  g.validate
  -- (2) Build partnerIdx.
  --     For each dart position i, resolve the partner label to its position
  --     in raw.darts.  Safe: g.partner[i]! ∈ g.darts (check 6 of validate).
  let n := g.darts.size
  let partnerIdx ← (List.range n).toArray.mapM fun i => do
    let p := g.partner[i]!
    match findPos g.darts p with
    | some j => return j
    | none   => throw s!"internal: partner label {p} not found after validation"
  -- (3) Build vertexIdx.
  --     For each dart position i, resolve the vertex label to its position
  --     in raw.vertices.  Safe: g.vertexOf[i]! ∈ g.vertices (check 5).
  let vertexIdx ← (List.range n).toArray.mapM fun i => do
    let v := g.vertexOf[i]!
    match findPos g.vertices v with
    | some j => return j
    | none   => throw s!"internal: vertex label {v} not found after validation"
  return { raw := g, partnerIdx, vertexIdx }
