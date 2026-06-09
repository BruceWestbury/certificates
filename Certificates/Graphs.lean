import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Basic

/-!
# Core graph structures — finite type formulation

`ClosedGraph` and `OpenGraph` carry their dart and vertex sets as abstract
`Type` fields, with `Fintype` and `DecidableEq` stored as plain structure
fields.  This restricts `partner` and `vertex` to their proper domains:
passing a dart from a different graph is a type error.

Instance fields are introduced locally with `letI` wherever typeclass
synthesis is needed.  They are NOT registered as global instances to avoid
polluting the instance search.
-/

-- ============================================================
-- ClosedGraph
-- ============================================================

/-- A closed dart graph: a fixed-point-free involution on darts and an
    incidence map.  No boundary darts. -/
structure ClosedGraph where
  Dart          : Type
  Vertex        : Type
  dartFintype   : Fintype Dart
  vertexFintype : Fintype Vertex
  dartDecEq     : DecidableEq Dart
  vertexDecEq   : DecidableEq Vertex
  partner       : Dart → Dart
  vertex        : Dart → Vertex

/-- A `ClosedGraph` is valid when `partner` is a fixed-point-free involution
    and every vertex has valence 2 or 3. -/
def ClosedGraph.valid (g : ClosedGraph) : Bool :=
  letI := g.dartFintype
  letI := g.vertexFintype
  letI := g.dartDecEq
  letI := g.vertexDecEq
  -- (1) partner is an involution: partner (partner d) = d
  decide (∀ d : g.Dart, g.partner (g.partner d) = d)
  -- (2) no fixed points: partner d ≠ d
  && decide (∀ d : g.Dart, g.partner d ≠ d)
  -- (3) every vertex has valence 2 or 3
  && decide (∀ v : g.Vertex,
       (Finset.univ.filter (fun d => g.vertex d = v)).card = 2 ∨
       (Finset.univ.filter (fun d => g.vertex d = v)).card = 3)

-- ============================================================
-- OpenGraph
-- ============================================================

/-- A dart graph with boundary: some darts are unpaired (the boundary),
    the rest are paired by `partner`.  The boundary list is ordered. -/
structure OpenGraph where
  Dart          : Type
  Vertex        : Type
  dartFintype   : Fintype Dart
  vertexFintype : Fintype Vertex
  dartDecEq     : DecidableEq Dart
  vertexDecEq   : DecidableEq Vertex
  boundary      : List Dart
  partner       : Dart → Option Dart
  vertex        : Dart → Vertex

/-- An `OpenGraph` is valid when:
    boundary darts have no partner; non-boundary darts have a partner;
    `partner` is symmetric and fixed-point-free;
    `boundary` has no duplicates; every vertex has valence 2 or 3. -/
def OpenGraph.valid (g : OpenGraph) : Bool :=
  letI := g.dartFintype
  letI := g.vertexFintype
  letI := g.dartDecEq
  letI := g.vertexDecEq
  -- (1) boundary darts have no partner
  decide (∀ d : g.Dart, d ∈ g.boundary → g.partner d = none)
  -- (2) non-boundary darts have a partner
  && decide (∀ d : g.Dart, d ∉ g.boundary → g.partner d ≠ none)
  -- (3) partner is symmetric where defined
  && decide (∀ d e : g.Dart, g.partner d = some e → g.partner e = some d)
  -- (4) no dart is its own partner
  && decide (∀ d : g.Dart, g.partner d ≠ some d)
  -- (5) boundary has no duplicates
  && decide (g.boundary.Nodup)
  -- (6) every vertex has valence 2 or 3
  && decide (∀ v : g.Vertex,
       (Finset.univ.filter (fun d => g.vertex d = v)).card = 2 ∨
       (Finset.univ.filter (fun d => g.vertex d = v)).card = 3)

-- ============================================================
-- Occurrence
-- ============================================================

/-- An occurrence of `L : OpenGraph` inside `G : ClosedGraph`: a pair of
    injective maps embedding L's darts and vertices into G's, preserving
    incidence, interior pairings, and boundary structure. -/
structure Occurrence (L : OpenGraph) (G : ClosedGraph) where
  dartMap   : L.Dart → G.Dart
  vertexMap : L.Vertex → G.Vertex

def Occurrence.valid {L : OpenGraph} {G : ClosedGraph} (o : Occurrence L G) : Bool :=
  letI := L.dartFintype;   letI := G.dartFintype
  letI := L.vertexFintype; letI := G.vertexFintype
  letI := L.dartDecEq;     letI := G.dartDecEq
  letI := L.vertexDecEq;   letI := G.vertexDecEq
  -- (1) dartMap is injective
  decide (Function.Injective o.dartMap)
  -- (2) vertexMap is injective
  && decide (Function.Injective o.vertexMap)
  -- (3) preserves incidence: G.vertex (dartMap d) = vertexMap (L.vertex d)
  && decide (∀ d : L.Dart, G.vertex (o.dartMap d) = o.vertexMap (L.vertex d))
  -- (4) preserves interior pairings: L.partner d = some e → G.partner (dartMap d) = dartMap e
  && decide (∀ d e : L.Dart, L.partner d = some e → G.partner (o.dartMap d) = o.dartMap e)
  -- (5) boundary structure: G-partner of each boundary-dart image is outside the image
  && decide (∀ b : L.Dart, b ∈ L.boundary →
       G.partner (o.dartMap b) ∉ Finset.univ.image o.dartMap)

-- ============================================================
-- Complement
-- ============================================================

/-!
The complement `G / L` of an occurrence `o : Occurrence L G`.

`CompDart`   = G-darts NOT in the image of `o.dartMap`.
`CompVertex` = G-vertices incident to at least one `CompDart`.

Using `CompVertex` (rather than all of `G.Vertex`) ensures that the vertices
of the removed pattern do not survive as isolated valence-0 vertices.

The `vertex` map sends each complement dart `d` to the subtype witness
`⟨G.vertex d.1, ⟨d, rfl⟩⟩`; no membership proof is needed because
`CompVertex` is defined as exactly the set touched by complement darts.

Marked `abbrev` so that `Replacement.iso` can see the concrete types.
-/
abbrev Occurrence.complement {L : OpenGraph} {G : ClosedGraph}
    (o : Occurrence L G) : OpenGraph :=
  letI := L.dartFintype;   letI := G.dartFintype
  letI := L.dartDecEq;     letI := G.dartDecEq
  letI := G.vertexFintype; letI := G.vertexDecEq
  let img        : Finset G.Dart := Finset.univ.image o.dartMap
  let CompDart   := { d : G.Dart // d ∉ img }
  let CompVertex := { v : G.Vertex // ∃ d : CompDart, G.vertex d.1 = v }
  { Dart          := CompDart
    Vertex        := CompVertex
    dartFintype   := inferInstance
    vertexFintype := inferInstance
    dartDecEq     := inferInstance
    vertexDecEq   := inferInstance
    boundary      := L.boundary.filterMap fun b =>
                       let gp := G.partner (o.dartMap b)
                       if h : gp ∉ img then some ⟨gp, h⟩ else none
    partner       := fun ⟨d, _⟩ =>
                       let gp := G.partner d
                       if h : gp ∉ img then some ⟨gp, h⟩ else none
    vertex        := fun d => ⟨G.vertex d.1, ⟨d, rfl⟩⟩ }

-- ============================================================
-- After-occurrence extensions (bivalent-vertex overlap)
-- ============================================================

/-!
In the new certificate design, a bivalent vertex of the RHS graph R may have
both its incident darts on the boundary of R.  When embedded via the
after-occurrence, those two image darts are partners in H and are allowed to
lie in both the occurrence image and the complement boundary simultaneously.

Three additions support this:
1. `OpenGraph.bivalentBoundaryDarts` — identifies the eligible boundary darts.
2. `Occurrence.validAfter`           — relaxed validity for after-occurrences.
3. `Occurrence.afterComplement`      — extended complement including overlap darts.
-/

/-- The boundary darts of `R` whose vertex has exactly two incident darts,
    both of which are boundary darts.  These are the darts eligible for the
    overlap between occurrence image and complement. -/
def OpenGraph.bivalentBoundaryDarts (R : OpenGraph) : Finset R.Dart :=
  letI := R.dartFintype; letI := R.dartDecEq; letI := R.vertexDecEq
  R.boundary.toFinset.filter fun d =>
    let vDarts := Finset.univ.filter (fun e => R.vertex e = R.vertex d)
    vDarts.card = 2 ∧ vDarts ⊆ R.boundary.toFinset

/-- Relaxed validity for after-occurrences.

    Conditions (1)–(4) are identical to `Occurrence.valid`.
    Condition (5) is split into two cases:

    (5a) Ordinary boundary darts (`b ∉ bivalentBoundaryDarts`): the
         H-partner of the image lies outside the image, as before.

    (5b) Bivalent boundary darts (`b ∈ bivalentBoundaryDarts`): the two
         image darts for the bivalent vertex are H-partners of each other.
         Both will appear on the after-complement boundary. -/
def Occurrence.validAfter {R : OpenGraph} {H : ClosedGraph} (o : Occurrence R H) : Bool :=
  letI := R.dartFintype;   letI := H.dartFintype
  letI := R.vertexFintype; letI := H.vertexFintype
  letI := R.dartDecEq;     letI := H.dartDecEq
  letI := R.vertexDecEq;   letI := H.vertexDecEq
  -- (1) dartMap is injective
  decide (Function.Injective o.dartMap)
  -- (2) vertexMap is injective
  && decide (Function.Injective o.vertexMap)
  -- (3) preserves incidence
  && decide (∀ d : R.Dart, H.vertex (o.dartMap d) = o.vertexMap (R.vertex d))
  -- (4) preserves interior pairings
  && decide (∀ d e : R.Dart, R.partner d = some e → H.partner (o.dartMap d) = o.dartMap e)
  -- (5a) ordinary boundary darts: H-partner of image is outside the image
  && decide (∀ b : R.Dart, b ∈ R.boundary → b ∉ R.bivalentBoundaryDarts →
       H.partner (o.dartMap b) ∉ Finset.univ.image o.dartMap)
  -- (5b) bivalent boundary darts: the two image darts are H-partners
  && decide (∀ b : R.Dart, b ∈ R.bivalentBoundaryDarts →
       ∃ e : R.Dart, e ∈ R.bivalentBoundaryDarts
         ∧ R.vertex e = R.vertex b ∧ e ≠ b
         ∧ H.partner (o.dartMap b) = o.dartMap e)

/-- Extended complement for an after-occurrence.

    The dart set includes:
    - all H-darts outside the occurrence image (regular complement darts), and
    - images of bivalent boundary darts (overlap darts, in both image and complement).

    The boundary is constructed by a **single pass through `R.boundary`** to
    preserve the RHS boundary order (required for the iso boundary check):
    - ordinary boundary dart b: contribute H.partner (o.dartMap b) as before;
    - bivalent boundary dart b: contribute o.dartMap b itself. -/
abbrev Occurrence.afterComplement {R : OpenGraph} {H : ClosedGraph}
    (o : Occurrence R H) : OpenGraph :=
  letI := R.dartFintype;   letI := H.dartFintype
  letI := R.dartDecEq;     letI := H.dartDecEq
  letI := R.vertexDecEq                           -- needed by bivalentBoundaryDarts
  letI := H.vertexFintype; letI := H.vertexDecEq
  let img     : Finset H.Dart := Finset.univ.image o.dartMap
  let overlap : Finset H.Dart := R.bivalentBoundaryDarts.image o.dartMap
  let ACompDart   := { d : H.Dart // d ∉ img ∨ d ∈ overlap }
  let ACompVertex := { v : H.Vertex // ∃ d : ACompDart, H.vertex d.1 = v }
  { Dart          := ACompDart
    Vertex        := ACompVertex
    dartFintype   := inferInstance
    vertexFintype := inferInstance
    dartDecEq     := inferInstance
    vertexDecEq   := inferInstance
    -- Single pass preserves RHS boundary order exactly.
    boundary      := R.boundary.filterMap (fun b =>
                       if b ∈ R.bivalentBoundaryDarts then
                         -- Bivalent case: contribute the image dart itself.
                         let d := o.dartMap b
                         if h : d ∉ img ∨ d ∈ overlap then some (⟨d, h⟩ : ACompDart)
                         else none
                       else
                         -- Ordinary case: contribute H.partner of the image,
                         -- exactly as in Occurrence.complement.
                         let gp := H.partner (o.dartMap b)
                         if h : gp ∉ img ∨ gp ∈ overlap then some (⟨gp, h⟩ : ACompDart)
                         else none)
    partner       := fun ⟨d, _⟩ =>
                       let gp := H.partner d
                       if h : gp ∉ img ∨ gp ∈ overlap then some (⟨gp, h⟩ : ACompDart)
                       else none
    vertex        := fun d => ⟨H.vertex d.1, ⟨d, rfl⟩⟩ }

-- ============================================================
-- Isomorphism
-- ============================================================

/-- An isomorphism between two open graphs: bijections on darts and vertices
    preserving incidence, partner, and (ordered) boundary. -/
structure Isomorphism (C1 C2 : OpenGraph) where
  dartMap   : C1.Dart → C2.Dart
  vertexMap : C1.Vertex → C2.Vertex

def Isomorphism.valid {C1 C2 : OpenGraph} (iso : Isomorphism C1 C2) : Bool :=
  letI := C1.dartFintype;   letI := C2.dartFintype
  letI := C1.vertexFintype; letI := C2.vertexFintype
  letI := C1.dartDecEq;     letI := C2.dartDecEq
  letI := C1.vertexDecEq;   letI := C2.vertexDecEq
  -- (1) dartMap is a bijection
  decide (Function.Injective  iso.dartMap)
  && decide (Function.Surjective iso.dartMap)
  -- (2) vertexMap is a bijection
  && decide (Function.Injective  iso.vertexMap)
  && decide (Function.Surjective iso.vertexMap)
  -- (3) preserves vertex incidence
  && decide (∀ d : C1.Dart, C2.vertex (iso.dartMap d) = iso.vertexMap (C1.vertex d))
  -- (4) preserves partner: C2.partner (dartMap d) = (C1.partner d).map dartMap
  && decide (∀ d : C1.Dart, C2.partner (iso.dartMap d) = (C1.partner d).map iso.dartMap)
  -- (5) preserves boundary order: the i-th boundary dart maps to the i-th
  && (C1.boundary.length == C2.boundary.length)
  && (C1.boundary.zip C2.boundary).all (fun p => iso.dartMap p.1 == p.2)

-- ============================================================
-- Replacement
-- ============================================================

/-!
A replacement certificate asserts that the complement of occurrence `before`
(embedding `L` in `G`) is isomorphic to the complement of occurrence `after`
(embedding `R` in `H`), with matching ordered boundary.

The common data `L`, `R`, `G`, and `before` are type parameters rather than
fields.  This eliminates redundant storage and lets theorem statements share
these quantities by unification rather than by explicit equality hypotheses
or `HEq`.

Because `Occurrence.complement` and `Occurrence.afterComplement` are `abbrev`s,
the `iso` field's dart map has the concrete subtype
  `{ d : G.Dart // d ∉ img_before } → { d : H.Dart // d ∉ img_after ∨ d ∈ overlap }`,
so the type system enforces that maps stay within complement darts.

The `before` complement is the strict complement (no overlap allowed).
The `after` complement is the extended complement that admits the overlap
with bivalent-boundary dart images.
-/
structure Replacement
    (L R  : OpenGraph)
    (G H  : ClosedGraph)
    (before : Occurrence L G) where
  after : Occurrence R H
  iso   : Isomorphism before.complement after.afterComplement

/-- A `Replacement` is valid when all components are well-formed, the
    isomorphism correctly connects the two complements, and the boundary
    ordering is compatible: applying `iso` to the complement boundary darts
    of the left occurrence gives exactly the complement boundary darts of
    the right occurrence, in the same order. -/
def Replacement.valid
    {L R  : OpenGraph}
    {G H  : ClosedGraph}
    {before : Occurrence L G}
    (r : Replacement L R G H before) : Bool :=
  L.valid
  && G.valid
  && R.valid
  && H.valid
  && before.valid             -- before occurrence: strict validity
  && r.after.validAfter       -- after occurrence: relaxed validity (bivalent exception)
  && before.complement.valid
  && r.after.afterComplement.valid   -- after complement: extended dart set
  && r.iso.valid
  -- Ordered boundary compatibility:
  --   before.complement.boundary[i]
  --     = G-partner of before.dartMap (L.boundary[i])
  --   applying iso maps it to r.after.afterComplement.boundary[i], which is:
  --     ordinary dart  → H-partner of after.dartMap (R.boundary[i])
  --     bivalent dart  → after.dartMap (R.boundary[i]) itself
  && (letI := r.after.afterComplement.dartDecEq
      decide (before.complement.boundary.map r.iso.dartMap =
              r.after.afterComplement.boundary))

-- ============================================================
-- Uniqueness of substitution up to isomorphism
-- ============================================================

/-- Two closed dart graphs are isomorphic if there exist bijections on darts
    and vertices that commute with `partner` and `vertex`. -/
def ClosedGraph.IsIso (G H : ClosedGraph) : Prop :=
  ∃ (f : G.Dart → H.Dart) (g : G.Vertex → H.Vertex),
    Function.Bijective f ∧
    Function.Bijective g ∧
    (∀ d : G.Dart, H.partner (f d) = f (G.partner d)) ∧
    (∀ d : G.Dart, H.vertex  (f d) = g (G.vertex  d))

/-!
### Uniqueness of substitution up to isomorphism

If two valid replacement certificates share the same host `G`, pattern `L`,
occurrence `before : Occurrence L G`, and replacement `R`, then their result
graphs `H₁` and `H₂` are isomorphic as closed dart graphs.

With the parameterised structure the shared data is a type parameter, so
both certificates literally have the same `L`, `R`, `G`, `before`; no
equality hypotheses or `HEq` are needed.

Proof: omitted (`sorry`).  The argument would construct the isomorphism
explicitly from the two isomorphisms `r₁.iso` and `r₂.iso`, both of which
map from the same complement `before.complement`, and then use the ordered
boundary compatibility to show the two gluings produce isomorphic results.
-/
theorem Replacement.unique_up_to_iso
    {L R   : OpenGraph}
    {G H₁ H₂ : ClosedGraph}
    {before : Occurrence L G}
    (r₁  : Replacement L R G H₁ before)
    (r₂  : Replacement L R G H₂ before)
    (hv₁ : r₁.valid = true)
    (hv₂ : r₂.valid = true) :
    ClosedGraph.IsIso H₁ H₂ := by
  sorry

-- ============================================================
-- Stage 1: Valence helpers
-- ============================================================

/-- The number of darts incident to vertex `v` in `G`. -/
def ClosedGraph.valence (G : ClosedGraph) (v : G.Vertex) : Nat :=
  letI := G.dartFintype
  letI := G.vertexDecEq
  (Finset.univ.filter (fun d => G.vertex d = v)).card

/-- True iff vertex `v` has exactly two incident darts. -/
def ClosedGraph.isBivalent (G : ClosedGraph) (v : G.Vertex) : Bool :=
  G.valence v == 2

/-- The finset of all bivalent (valence-2) vertices of `G`. -/
def ClosedGraph.bivalentVertices (G : ClosedGraph) : Finset G.Vertex :=
  letI := G.vertexFintype
  Finset.univ.filter (fun v => G.valence v = 2)

/-- True iff `G` has no bivalent vertices, i.e., every vertex has valence 3. -/
def ClosedGraph.isTrivalent (G : ClosedGraph) : Bool :=
  G.bivalentVertices.card = 0

-- ============================================================
-- Stage 2: SuppressionData
-- ============================================================

/-!
A `SuppressionData G` names the bivalent vertex to remove and its two
incident darts.  The `Prop`-valued fields document the mathematical intent;
`SuppressionData.valid` is the executable Boolean check.
-/
structure SuppressionData (G : ClosedGraph) where
  /-- The bivalent vertex to suppress. -/
  vertex    : G.Vertex
  /-- Its two incident darts. -/
  d₁ : G.Dart
  d₂ : G.Dart
  distinct  : d₁ ≠ d₂
  incident₁ : G.vertex d₁ = vertex
  incident₂ : G.vertex d₂ = vertex

/-- Checks that `{d₁, d₂}` is exactly the dart-set of `vertex`.
    This forces valence = 2 and confirms `d₁`, `d₂` are its only darts. -/
def SuppressionData.valid {G : ClosedGraph} (s : SuppressionData G) : Bool :=
  letI := G.dartFintype
  letI := G.dartDecEq
  letI := G.vertexDecEq
  decide (Finset.univ.filter (fun d => G.vertex d = s.vertex) = {s.d₁, s.d₂})

-- ============================================================
-- Stage 3: Suppression
-- ============================================================

/-!
## Bivalent-vertex suppression

`ClosedGraph.suppress s` removes `s.vertex` and its two darts `s.d₁`, `s.d₂`,
then reconnects the two surviving partner darts
`e₁ = G.partner s.d₁` and `e₂ = G.partner s.d₂` into a new edge.

Type-level design mirrors `Occurrence.complement`:

- **`NewDart`** = `{ d : G.Dart // d ∉ {s.d₁, s.d₂} }` — inherits `Fintype`
  and `DecidableEq` automatically.

- **`NewVertex`** = `{ v : G.Vertex // ∃ nd : NewDart, G.vertex nd.1 = v }` —
  vertices touched by at least one surviving dart, so `s.vertex` is excluded
  automatically (every dart incident to it is removed).

- **`partner`**: `e₁ ↦ e₂`, `e₂ ↦ e₁`; all other darts keep their old
  partner.  For valid suppression data, `e₁` and `e₂` are never in `removed`,
  so the `else ⟨d, hd⟩` fallback is unreachable.

- **`vertex`**: `fun d => ⟨G.vertex d.1, ⟨d, rfl⟩⟩`, identical to the
  complement construction — no proof obligations.
-/
abbrev ClosedGraph.suppress {G : ClosedGraph} (s : SuppressionData G) : ClosedGraph :=
  letI := G.dartFintype
  letI := G.dartDecEq
  letI := G.vertexFintype
  letI := G.vertexDecEq
  let removed : Finset G.Dart := {s.d₁, s.d₂}
  let e₁ : G.Dart := G.partner s.d₁   -- surviving partner of d₁
  let e₂ : G.Dart := G.partner s.d₂   -- surviving partner of d₂
  let NewDart   := { d : G.Dart // d ∉ removed }
  let NewVertex := { v : G.Vertex // ∃ nd : NewDart, G.vertex nd.1 = v }
  { Dart          := NewDart
    Vertex        := NewVertex
    dartFintype   := inferInstance
    vertexFintype := inferInstance
    dartDecEq     := inferInstance
    vertexDecEq   := inferInstance
    -- reconnect e₁ ↔ e₂; all other surviving darts keep G.partner
    partner       := fun ⟨d, hd⟩ =>
                       let gp := if d = e₁ then e₂
                                 else if d = e₂ then e₁
                                 else G.partner d
                       if h : gp ∉ removed then ⟨gp, h⟩ else ⟨d, hd⟩
    vertex        := fun d => ⟨G.vertex d.1, ⟨d, rfl⟩⟩ }

-- ============================================================
-- Stage 4: Example — modified theta graph
-- ============================================================

/-!
### Modified theta graph

Two trivalent vertices A (= 0) and B (= 1), one bivalent vertex C (= 2).

```
A ─[0,1]──────── B     (edge 1)
A ─[2,3]──────── B     (edge 2)
A ─[4,6]─ C ─[7,5]─ B (path through C)
```

Partner pairings: 0 ↔ 1, 2 ↔ 3, 4 ↔ 6, 5 ↔ 7.

Suppressing C reconnects dart 4 (at A) to dart 5 (at B),
recovering the plain theta graph with partner pairings 0↔1, 2↔3, 4↔5.
-/
abbrev modifiedTheta : ClosedGraph where
  Dart          := Fin 8
  Vertex        := Fin 3
  dartFintype   := inferInstance
  vertexFintype := inferInstance
  dartDecEq     := inferInstance
  vertexDecEq   := inferInstance
  partner       := fun d => match d.val with
                     | 0 => 1 | 1 => 0
                     | 2 => 3 | 3 => 2
                     | 4 => 6 | 6 => 4
                     | 5 => 7 | 7 => 5
                     | _ => 0  -- unreachable (Fin 8 has values 0–7 only)
  vertex        := fun d => match d.val with
                     | 0 | 2 | 4 => 0  -- vertex A
                     | 1 | 3 | 5 => 1  -- vertex B
                     | _         => 2  -- vertex C (darts 6, 7)

/-- Suppress vertex C (Fin 3 value 2) via its two incident darts 6 and 7.
    With `abbrev modifiedTheta`, the field types reduce to `Fin 8` / `Fin 3`,
    so `by decide` can evaluate all proof obligations concretely. -/
def suppressC : SuppressionData modifiedTheta where
  vertex    := ⟨2, by decide⟩   -- vertex C : Fin 3
  d₁        := ⟨6, by decide⟩   -- dart 6  : Fin 8
  d₂        := ⟨7, by decide⟩   -- dart 7  : Fin 8
  distinct  := by decide           -- 6 ≠ 7 as Fin 8
  incident₁ := by decide           -- modifiedTheta.vertex 6 = 2
  incident₂ := by decide           -- modifiedTheta.vertex 7 = 2

-- The original graph is valid (contains one bivalent vertex).
#eval modifiedTheta.valid                                           -- true
-- C is bivalent, so the graph is not yet trivalent.
#eval modifiedTheta.isTrivalent                                     -- false
-- The suppression data correctly identifies C and its two darts.
#eval suppressC.valid                                               -- true
-- After suppression the result is a valid closed graph.
#eval (modifiedTheta.suppress suppressC).valid                      -- true
-- Every vertex in the suppressed graph is trivalent.
#eval (modifiedTheta.suppress suppressC).isTrivalent                -- true
-- Dart count decreases by 2 (8 − 2 = 6).
#eval Fintype.card (modifiedTheta.suppress suppressC).Dart          -- 6
-- Vertex count decreases by 1 (3 − 1 = 2).
#eval Fintype.card (modifiedTheta.suppress suppressC).Vertex        -- 2




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
