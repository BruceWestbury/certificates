import Mathlib

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

Dart type: `{ d : G.Dart // d ∉ img }` where `img = Finset.univ.image o.dartMap`.
This subtype inherits `Fintype` and `DecidableEq` from `G.Dart` automatically.

Boundary: the G-partners of L's boundary-dart images — the darts "exposed"
when the pattern is removed.

`partner` of a complement dart `⟨d, _⟩`: compute `G.partner d`; if the result
lies outside `img` return it as a complement dart, otherwise return `none`
(meaning `d` is a boundary dart of the complement).

Marked `abbrev` so that `Replacement.iso` can see the concrete dart type.
-/
abbrev Occurrence.complement {L : OpenGraph} {G : ClosedGraph}
    (o : Occurrence L G) : OpenGraph :=
  letI := L.dartFintype;   letI := G.dartFintype
  letI := L.dartDecEq;     letI := G.dartDecEq
  letI := G.vertexFintype; letI := G.vertexDecEq
  let img : Finset G.Dart := Finset.univ.image o.dartMap
  { Dart          := { d : G.Dart // d ∉ img }
    Vertex        := G.Vertex
    dartFintype   := inferInstance
    vertexFintype := G.vertexFintype
    dartDecEq     := inferInstance
    vertexDecEq   := G.vertexDecEq
    boundary      := L.boundary.filterMap fun b =>
                       let gp := G.partner (o.dartMap b)
                       if h : gp ∉ img then some ⟨gp, h⟩ else none
    partner       := fun ⟨d, _⟩ =>
                       let gp := G.partner d
                       if h : gp ∉ img then some ⟨gp, h⟩ else none
    vertex        := fun ⟨d, _⟩ => G.vertex d }

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
A replacement certificate bundles two occurrences and an isomorphism between
their complements.

Because `Occurrence.complement` is an `abbrev`, the type of `iso` unfolds to
`Isomorphism { d : G.Dart // d ∉ img_before } { d : H.Dart // d ∉ img_after }`,
so the dart maps are correctly restricted to complement darts by the type system.
-/
structure Replacement where
  L      : OpenGraph
  G      : ClosedGraph
  R      : OpenGraph
  H      : ClosedGraph
  before : Occurrence L G
  after  : Occurrence R H
  iso    : Isomorphism before.complement after.complement

/-- A `Replacement` is valid when all components are well-formed and the
    isomorphism correctly connects the two computed complements. -/
def Replacement.valid (r : Replacement) : Bool :=
  r.L.valid
  && r.G.valid
  && r.R.valid
  && r.H.valid
  && r.before.valid
  && r.after.valid
  && r.before.complement.valid
  && r.after.complement.valid
  && r.iso.valid
