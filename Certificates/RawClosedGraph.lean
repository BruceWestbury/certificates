/-!
# Raw closed dart graph — validation layer

`RawClosedGraph` stores dart and vertex data exactly as it appears in a JSON
certificate: arbitrary `Nat` labels with no consecutive-numbering assumption.

`RawClosedGraph.validate` checks all structural and mathematical conditions
before any conversion to a typed `ClosedGraph`.

No imports are required; this file uses only Lean 4 core.
-/

/-- Raw representation of a closed dart graph from a JSON certificate.

    Parallel-array encoding:
    * `darts[i]`    — the label of the i-th dart (arbitrary `Nat`).
    * `vertices[j]` — the label of the j-th vertex (arbitrary `Nat`).
    * `vertexOf[i]` — the vertex label of dart `darts[i]`.
    * `partner[i]`  — the partner dart label of `darts[i]`.

    Labels are arbitrary natural numbers; positions in the arrays serve as
    the internal indices used during validation.  Values in `vertexOf` and
    `partner` are labels, not positions. -/
structure RawClosedGraph where
  darts    : Array Nat
  vertices : Array Nat
  vertexOf : Array Nat
  partner  : Array Nat
deriving Repr

-- ============================================================
-- Array helpers (private)
-- ============================================================

/-- True iff `x` appears anywhere in `xs`. -/
private def Array.containsNat (xs : Array Nat) (x : Nat) : Bool :=
  Id.run do
    for y in xs do
      if y == x then return true
    return false

/-- The index of the first element of `xs` equal to `x`, or `none`.
    The returned index `i` satisfies `i < xs.size` by construction. -/
private def Array.indexOfNat? (xs : Array Nat) (x : Nat) : Option Nat :=
  Id.run do
    for i in List.range xs.size do
      if xs[i]! == x then return some i
    return none

/-- True iff `xs` contains at least two equal elements.  O(n²). -/
private def Array.hasDuplicatesNat (xs : Array Nat) : Bool :=
  Id.run do
    for i in List.range xs.size do
      for j in List.range i do          -- j < i < xs.size, so both accesses are safe
        if xs[i]! == xs[j]! then return true
    return false

-- ============================================================
-- Validation
-- ============================================================

/-- Validate a `RawClosedGraph`.

    Checks are performed in the order listed; the first failure is returned
    as `Except.error` with a message identifying the offending entry.

    1. `vertexOf.size = darts.size`
    2. `partner.size = darts.size`
    3. dart labels are distinct
    4. vertex labels are distinct
    5. every `vertexOf` value is a known vertex label
    6. every `partner` value is a known dart label
    7. `partner` is an involution on labels:
       for each position `i`, let `d = darts[i]` and `p = partner[i]`;
       find position `j` with `darts[j] = p`;
       require `partner[j] = d`
    8. `partner` has no fixed points: `partner[i] ≠ darts[i]` -/
def RawClosedGraph.validate (g : RawClosedGraph) : Except String Unit := do
  -- (1) vertexOf is parallel to darts.
  if g.vertexOf.size ≠ g.darts.size then
    throw s!"vertexOf has {g.vertexOf.size} entries but darts has {g.darts.size}"
  -- (2) partner is parallel to darts.
  if g.partner.size ≠ g.darts.size then
    throw s!"partner has {g.partner.size} entries but darts has {g.darts.size}"
  -- (3) Dart labels must be distinct.
  if g.darts.hasDuplicatesNat then
    throw "darts contains duplicate labels"
  -- (4) Vertex labels must be distinct.
  if g.vertices.hasDuplicatesNat then
    throw "vertices contains duplicate labels"
  -- (5) Every vertexOf entry must be a known vertex label.
  for i in List.range g.darts.size do
    let v := g.vertexOf[i]!
    if !g.vertices.containsNat v then
      throw s!"vertexOf[{i}] = {v} is not a vertex label (dart {g.darts[i]!})"
  -- (6) Every partner entry must be a known dart label.
  for i in List.range g.darts.size do
    let p := g.partner[i]!
    if !g.darts.containsNat p then
      throw s!"partner[{i}] = {p} is not a dart label (dart {g.darts[i]!})"
  -- (7) partner must be an involution on labels.
  --     For each dart d = darts[i] with partner label p = partner[i]:
  --       find j with darts[j] = p  (exists because check (6) passed),
  --       then require partner[j] = d.
  --     partner[j] is safe: j < darts.size = partner.size (check (2)).
  for i in List.range g.darts.size do
    let d := g.darts[i]!
    let p := g.partner[i]!
    match g.darts.indexOfNat? p with
    | none   =>
      -- Unreachable: check (6) confirmed p is a dart label.
      throw s!"internal: dart label {p} not found in darts"
    | some j =>
      let pp := g.partner[j]!
      if pp ≠ d then
        throw s!"partner not an involution: partner(partner({d})) = {pp} ≠ {d}"
  -- (8) partner must have no fixed points.
  for i in List.range g.darts.size do
    if g.partner[i]! == g.darts[i]! then
      throw s!"partner has a fixed point at dart {g.darts[i]!}"
