import Main

/-!
Small graph constructions using `Fin n` for dart and vertex types.

`Fintype (Fin n)` and `DecidableEq (Fin n)` are available in Lean 4 core;
`inferInstance` resolves them without any extra import.

`partner` is defined by `match d.val with` on the underlying `Nat`.
`vertex`  is defined by `if d.val < k then …` chains or `match d.val with`.

The `#eval` lines at the bottom run `OpenGraph.valid` on each graph and
should all print `true`.
-/

-- ============================================================
-- Atomic graphs
-- ============================================================

/-- One bivalent vertex, two boundary darts.
    Python: `_edge_graph()` -/
def edgeGraph : OpenGraph where
  Dart          := Fin 2
  Vertex        := Fin 1
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 1]
  partner       := fun _ => none
  vertex        := fun _ => 0

/-- One trivalent vertex, three boundary darts.
    Python: `_vertex_graph()` -/
def vertexGraph : OpenGraph where
  Dart          := Fin 3
  Vertex        := Fin 1
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 1, 2]
  partner       := fun _ => none
  vertex        := fun _ => 0

/-- One trivalent vertex, one boundary dart, one internal loop (darts 1 ↔ 2).
    Python: `_lollipop_graph()` -/
def lollipopGraph : OpenGraph where
  Dart          := Fin 3
  Vertex        := Fin 1
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0]
  partner       := fun d => match d.val with
                     | 1 => some 2
                     | 2 => some 1
                     | _ => none
  vertex        := fun _ => 0

-- ============================================================
-- Polygon graphs
-- ============================================================

/-!
For `_polygon_graph(k)` the dart layout is:
  darts `3i`, `3i+1`, `3i+2`  ↦  vertex `i`   (i = 0, …, k−1)
  boundary = [0, 3, 6, …]
  internal edges: `3i+2 ↔ 3((i+1) mod k)+1`
-/

/-- Two trivalent vertices, two parallel edges, two boundary darts.
    Boundary: [0, 3].  Interior edges: 2↔4, 1↔5.
    Python: `_bigon_graph()` = `_polygon_graph(2)` -/
def bigonGraph : OpenGraph where
  Dart          := Fin 6
  Vertex        := Fin 2
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 3]
  partner       := fun d => match d.val with
                     | 1 => some 5
                     | 5 => some 1
                     | 2 => some 4
                     | 4 => some 2
                     | _ => none
  vertex        := fun d => if d.val < 3 then 0 else 1

/-- Three trivalent vertices in a cycle, three boundary darts.
    Boundary: [0, 3, 6].  Interior edges: 2↔4, 5↔7, 8↔1.
    Python: `_triangle_graph()` = `_polygon_graph(3)` -/
def triangleGraph : OpenGraph where
  Dart          := Fin 9
  Vertex        := Fin 3
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 3, 6]
  partner       := fun d => match d.val with
                     | 1 => some 8
                     | 8 => some 1
                     | 2 => some 4
                     | 4 => some 2
                     | 5 => some 7
                     | 7 => some 5
                     | _ => none
  vertex        := fun d =>
                     if d.val < 3 then 0
                     else if d.val < 6 then 1
                     else 2

/-- Four trivalent vertices in a cycle, four boundary darts.
    Boundary: [0, 3, 6, 9].  Interior edges: 2↔4, 5↔7, 8↔10, 11↔1.
    Python: `_square_graph()` = `_polygon_graph(4)` -/
def squareGraph : OpenGraph where
  Dart          := Fin 12
  Vertex        := Fin 4
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 3, 6, 9]
  partner       := fun d => match d.val with
                     | 1  => some 11
                     | 11 => some 1
                     | 2  => some 4
                     | 4  => some 2
                     | 5  => some 7
                     | 7  => some 5
                     | 8  => some 10
                     | 10 => some 8
                     | _  => none
  vertex        := fun d =>
                     if d.val < 3 then 0
                     else if d.val < 6 then 1
                     else if d.val < 9 then 2
                     else 3

-- ============================================================
-- Six-term relation graphs  (4 boundary darts, 1 internal edge)
-- ============================================================

/-- K: boundary darts 0–3; internal edge 4↔5.
    Vertex 0 = {0,1,4},  vertex 1 = {2,3,5}.
    Python: `K()` -/
def graphK : OpenGraph where
  Dart          := Fin 6
  Vertex        := Fin 2
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 1, 2, 3]
  partner       := fun d => match d.val with
                     | 4 => some 5
                     | 5 => some 4
                     | _ => none
  vertex        := fun d => match d.val with
                     | 2 | 3 | 5 => 1
                     | _         => 0

/-- H: boundary darts 0–3; internal edge 4↔5.
    Vertex 0 = {0,3,4},  vertex 1 = {1,2,5}.
    Python: `H()` -/
def graphH : OpenGraph where
  Dart          := Fin 6
  Vertex        := Fin 2
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 1, 2, 3]
  partner       := fun d => match d.val with
                     | 4 => some 5
                     | 5 => some 4
                     | _ => none
  vertex        := fun d => match d.val with
                     | 1 | 2 | 5 => 1
                     | _         => 0

/-- A: boundary darts 0–3; internal edge 4↔5.
    Vertex 0 = {0,2,5},  vertex 1 = {1,3,4}.
    Python: `A()` -/
def graphA : OpenGraph where
  Dart          := Fin 6
  Vertex        := Fin 2
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 1, 2, 3]
  partner       := fun d => match d.val with
                     | 4 => some 5
                     | 5 => some 4
                     | _ => none
  vertex        := fun d => match d.val with
                     | 1 | 3 | 4 => 1
                     | _         => 0

-- ============================================================
-- Six-term relation graphs  (4 boundary darts, no internal edges)
-- ============================================================

/-- U: boundary darts 0–3; no internal edges.
    Vertex 0 = {0,1},  vertex 1 = {2,3}.
    Python: `U()` -/
def graphU : OpenGraph where
  Dart          := Fin 4
  Vertex        := Fin 2
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 1, 2, 3]
  partner       := fun _ => none
  vertex        := fun d => match d.val with
                     | 2 | 3 => 1
                     | _     => 0

/-- I: boundary darts 0–3; no internal edges.
    Vertex 0 = {0,3},  vertex 1 = {1,2}.
    Python: `I()` -/
def graphI : OpenGraph where
  Dart          := Fin 4
  Vertex        := Fin 2
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 1, 2, 3]
  partner       := fun _ => none
  vertex        := fun d => match d.val with
                     | 1 | 2 => 1
                     | _     => 0

/-- X: boundary darts 0–3; no internal edges.
    Vertex 0 = {0,2},  vertex 1 = {1,3}.
    Python: `X()` -/
def graphX : OpenGraph where
  Dart          := Fin 4
  Vertex        := Fin 2
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  boundary      := [0, 1, 2, 3]
  partner       := fun _ => none
  vertex        := fun d => match d.val with
                     | 1 | 3 => 1
                     | _     => 0

-- ============================================================
-- Sanity checks
-- ============================================================

#eval edgeGraph.valid     -- expected: true
#eval vertexGraph.valid   -- expected: true
#eval lollipopGraph.valid -- expected: true
#eval bigonGraph.valid    -- expected: true
#eval triangleGraph.valid -- expected: true
#eval squareGraph.valid   -- expected: true
#eval graphK.valid        -- expected: true
#eval graphH.valid        -- expected: true
#eval graphA.valid        -- expected: true
#eval graphU.valid        -- expected: true
#eval graphI.valid        -- expected: true
#eval graphX.valid        -- expected: true
