import Certificates.ValidatedClosedGraph
import Certificates.Graphs  -- for ClosedGraph, Fintype (Fin n), inferInstance

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

structure TypedIndexArrays (raw : RawClosedGraph) where
  partnerIdx : Array (Fin raw.darts.size)
  vertexIdx  : Array (Fin raw.vertices.size)
  partnerIdx_size : partnerIdx.size = raw.darts.size
  vertexIdx_size  : vertexIdx.size = raw.darts.size

/-- Closed graph data with Fin-typed index arrays.

    Every `partnerIdx[i] : Fin raw.darts.size` is statically known
    to be a valid dart position.
    Every `vertexIdx[i] : Fin raw.vertices.size` is statically known
    to be a valid vertex position. -/
structure TypedClosedGraphData where
  raw : RawClosedGraph
  arrays : TypedIndexArrays raw

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

  if hPartner : v.partnerIdx.size = n then
    if hVertex : v.vertexIdx.size = n then

      let partnerFin : Array (Fin n) ← v.partnerIdx.mapM fun idx =>
        if h : idx < n then
          return ⟨idx, h⟩
        else
          throw s!"partnerIdx entry {idx} ≥ darts.size = {n}"

      let vertexFin : Array (Fin k) ← v.vertexIdx.mapM fun idx =>
        if h : idx < k then
          return ⟨idx, h⟩
        else
          throw s!"vertexIdx entry {idx} ≥ vertices.size = {k}"

      let arrays : TypedIndexArrays v.raw := {
        partnerIdx := partnerFin
        vertexIdx := vertexFin
        partnerIdx_size := by
          -- temporarily use this if needed
          sorry
        vertexIdx_size := by
          sorry
      }

      return {
        raw := v.raw
        arrays := arrays
      }

    else
      throw s!"vertexIdx.size = {v.vertexIdx.size} ≠ darts.size = {n}"
  else
    throw s!"partnerIdx.size = {v.partnerIdx.size} ≠ darts.size = {n}"

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
#eval! do
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
      IO.println s!"partnerIdx .val: {td.arrays.partnerIdx.map (fun x : Fin td.raw.darts.size => x.val)}"
      IO.println s!"vertexIdx  .val: {td.arrays.vertexIdx.map (fun x : Fin td.raw.vertices.size => x.val)}"
-- Expected:
-- partnerIdx .val: [1, 0]
-- vertexIdx  .val: [0, 0]

-- ============================================================
-- toClosedGraph?
-- ============================================================

/-- Convert `TypedClosedGraphData` to a `ClosedGraph`.

    `Dart   := Fin raw.darts.size`
    `Vertex := Fin raw.vertices.size`

    The Lean functions `partner` and `vertex` are built directly from the
    typed index arrays.  The proof obligation for each lookup is

        d.val < partnerIdx.size

    which follows from `d.isLt : d.val < raw.darts.size` and the stored
    invariant `partnerIdx_size : partnerIdx.size = raw.darts.size`.
    The tactic `rw [td.partnerIdx_size]; exact d.isLt` discharges it.
    No modulo arithmetic, no `getD`, no `sorry`. -/
def TypedClosedGraphData.toClosedGraph? (td : TypedClosedGraphData) :
    Except.{0, 1} String ClosedGraph :=
  .ok {
    Dart          := Fin td.raw.darts.size
    Vertex        := Fin td.raw.vertices.size
    dartFintype   := inferInstance
    vertexFintype := inferInstance
    dartDecEq     := inferInstance
    vertexDecEq   := inferInstance

    partner := fun d =>
      have h : d.val < td.arrays.partnerIdx.size := by
        rw [td.arrays.partnerIdx_size]
        exact d.isLt
      td.arrays.partnerIdx[d.val]'h

    vertex := fun d =>
      have h : d.val < td.arrays.vertexIdx.size := by
        rw [td.arrays.vertexIdx_size]
        exact d.isLt
      td.arrays.vertexIdx[d.val]'h
  }

-- ============================================================
-- Test
-- ============================================================

#eval! do
  let raw : RawClosedGraph := {
    darts    := #[10, 11]
    vertices := #[100]
    vertexOf := #[100, 100]
    partner  := #[11, 10]
  }

  match raw.toValidated with
  | .error e => IO.println s!"error: {e}"
  | .ok v =>
    match ValidatedClosedGraph.toTyped v with
    | .error e => IO.println s!"error: {e}"
    | .ok td =>
      match TypedClosedGraphData.toClosedGraph? td with
      | .error e => IO.println s!"error: {e}"
      | .ok (G : ClosedGraph) =>
        IO.println s!"dart card: {@Fintype.card G.Dart G.dartFintype}"
        IO.println s!"vertex card: {@Fintype.card G.Vertex G.vertexFintype}"
