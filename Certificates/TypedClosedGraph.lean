import Certificates.ValidatedClosedGraph

/-!
# Typed closed graph data — Fin-bounded index layer

`TypedClosedGraphData` promotes the untyped `Array Nat` index arrays of
`ValidatedClosedGraph` to `Array (Fin n)` and `Array (Fin k)`, so that Lean
statically knows every index is in range.

## Proof obligation

Converting `idx : Nat` to `Fin n` requires a proof `h : idx < n`.
We obtain it with `if h : idx < n then ⟨idx, h⟩ else throw …`.
This is the only proof obligation in this step.  No modulo, no `sorry`.

## Pipeline

    RawClosedGraph           label world  (arbitrary Nat labels)
          ↓  toValidated
    ValidatedClosedGraph     index world  (Array Nat, bounds not in types)
          ↓  toTyped  (this file)
    TypedClosedGraphData     Fin world    (Array (Fin n), bounds in types)
          ↓  toClosedGraph   (next step)
    ClosedGraph              function world (Fin n → Fin n, Fin n → Fin k)
-/



-- ============================================================
-- Structure
-- ============================================================

/-- Closed graph data with Fin-typed index arrays.

    Every `partnerIdx[i] : Fin raw.darts.size` is statically known
    to be a valid dart position.
    Every `vertexIdx[i] : Fin raw.vertices.size` is statically known
    to be a valid vertex position. -/
structure TypedClosedGraphData where
  raw        : RawClosedGraph
  partnerIdx : Array (Fin raw.darts.size)
  vertexIdx  : Array (Fin raw.vertices.size)

-- ============================================================
-- Conversion
-- ============================================================

/-- Convert `ValidatedClosedGraph` to `TypedClosedGraphData`.

    Steps:
    1. Check that the index arrays have the right size.
    2. For each `idx : Nat` in `partnerIdx`, check `idx < raw.darts.size`
       using a dependent `if h : …` and wrap it as `⟨idx, h⟩ : Fin n`.
    3. Do the same for `vertexIdx` against `raw.vertices.size`.

    The error branches in steps 2 and 3 are unreachable when `v` was
    produced by `RawClosedGraph.toValidated`, but they are required for
    exhaustiveness.  No modulo arithmetic is used. -/
def ValidatedClosedGraph.toTyped (v : ValidatedClosedGraph) :
    Except String TypedClosedGraphData := do
  let n := v.raw.darts.size
  let k := v.raw.vertices.size
  -- (1) Size checks
  if v.partnerIdx.size ≠ n then
    throw s!"partnerIdx.size = {v.partnerIdx.size} ≠ darts.size = {n}"
  if v.vertexIdx.size ≠ n then
    throw s!"vertexIdx.size = {v.vertexIdx.size} ≠ darts.size = {n}"
  -- (2) Lift partnerIdx entries to Fin n.
  --     `if h : idx < n` gives the proof `h` in the then-branch so that
  --     `⟨idx, h⟩ : Fin n` type-checks without modulo or sorry.
  let partnerFin : Array (Fin n) ← v.partnerIdx.mapM fun idx =>
    if h : idx < n then return ⟨idx, h⟩
    else throw s!"partnerIdx entry {idx} ≥ darts.size = {n}"
  -- (3) Lift vertexIdx entries to Fin k.
  let vertexFin : Array (Fin k) ← v.vertexIdx.mapM fun idx =>
    if h : idx < k then return ⟨idx, h⟩
    else throw s!"vertexIdx entry {idx} ≥ vertices.size = {k}"
  return { raw := v.raw, partnerIdx := partnerFin, vertexIdx := vertexFin }

-- ============================================================
-- Test
-- ============================================================

-- Darts [10, 11] (non-consecutive), vertices [100].
-- toValidated resolves:
--   partner of 10 = 11 → position 1   → partnerIdx[0] = 1
--   partner of 11 = 10 → position 0   → partnerIdx[1] = 0
--   vertex  of 10 = 100 → position 0  → vertexIdx[0]  = 0
--   vertex  of 11 = 100 → position 0  → vertexIdx[1]  = 0
-- toTyped wraps these as Fin 2 and Fin 1; .val recovers the Nat.
#eval do
  let raw : RawClosedGraph := {
    darts    := #[10, 11]
    vertices := #[100]
    vertexOf := #[100, 100]
    partner  := #[11, 10]
  }
  match raw.toValidated with
  | .error e => IO.println s!"validate error: {e}"
  | .ok v =>
    match v.toTyped with
    | .error e => IO.println s!"toTyped error: {e}"
    | .ok td =>
      IO.println s!"partnerIdx .val: {td.partnerIdx.toList.map (fun (x : Fin td.raw.darts.size) => x.val)}"
      IO.println s!"vertexIdx  .val: {td.vertexIdx.toList.map (fun (x : Fin td.raw.vertices.size) => x.val)}"
-- Expected:
-- partnerIdx .val: [1, 0]
-- vertexIdx  .val: [0, 0]
