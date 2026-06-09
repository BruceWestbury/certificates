import Certificates.Graphs
import Certificates.LinearCombinations

/-!
# Named local graph rules

This file sits between `Graphs` and `Reductions`.

It defines rule terms and named rules, together with the rule-level validity
condition needed for suppressed bivalent vertices:

  every bivalent vertex in a rule graph has both incident darts on the boundary.

The JSON schema can still name a rule; decoding/lookup will resolve that name
to one of the rules defined here.
-/

-- ============================================================
-- Rule-graph combinatorics
-- ============================================================

namespace OpenGraph

/-- The darts incident to a vertex, as a finite set. -/
def incidentDarts (g : OpenGraph) (v : g.Vertex) : Finset g.Dart :=
  letI := g.dartFintype
  letI := g.dartDecEq
  Finset.univ.filter (fun d => g.vertex d = v)

/-- The valence of a vertex. -/
def valence (g : OpenGraph) (v : g.Vertex) : Nat :=
  (g.incidentDarts v).card

/-- A vertex is bivalent when exactly two darts are incident to it. -/
def isBivalent (g : OpenGraph) (v : g.Vertex) : Bool :=
  g.valence v == 2

/-- The list of bivalent vertices. -/
def bivalentVertices (g : OpenGraph) : List g.Vertex :=
  letI := g.vertexFintype
  letI := g.vertexDecEq
  (Finset.univ.filter (fun v => g.isBivalent v)).toList

/-- If `v` is bivalent, return its two incident darts. -/
def bivalentPairAt? (g : OpenGraph) (v : g.Vertex) : Option (g.Dart × g.Dart) :=
  match (g.incidentDarts v).toList with
  | [a, b] => some (a, b)
  | _      => none

/-- All bivalent vertex dart-pairs in the graph.

There may be zero, one, or several such pairs. -/
def bivalentBoundaryPairs (g : OpenGraph) : List (g.Dart × g.Dart) :=
  g.bivalentVertices.filterMap (fun v => g.bivalentPairAt? v)

/-- The darts which pass through suppressed bivalent vertices. -/
def throughDarts (g : OpenGraph) : Finset g.Dart :=
  letI := g.dartDecEq
  (g.bivalentBoundaryPairs.foldl
    (fun s p => s.insert p.1 |>.insert p.2)
    (∅ : Finset g.Dart))

/-- Rule-level validity condition for bivalent vertices.

This does **not** say that every rule graph has bivalent vertices. It says:
if a bivalent vertex occurs, then both incident darts are boundary darts. -/
def validRuleGraph (g : OpenGraph) : Bool :=
  letI := g.vertexFintype
  letI := g.vertexDecEq
  letI := g.dartDecEq
  g.valid &&
  decide
    (∀ v : g.Vertex,
      g.valence v = 2 →
        ∀ d : g.Dart,
          d ∈ g.incidentDarts v →
            d ∈ g.boundary)

end OpenGraph

-- ============================================================
-- Rules
-- ============================================================

/-- One term on the right hand side of a local rule. -/
structure RuleTerm (R : Type) where
  coeff : R
  graph : OpenGraph

/-- A named local graph rule.

For now the RHS is stored as a list of terms rather than as `LC R OpenGraph`,
because `OpenGraph` itself is not intended to be a basis key with decidable
equality. The linear-combination layer will be used later for canonical graph
labels or decoded graph identifiers. -/
structure Rule (R : Type) where
  name : String
  lhs  : OpenGraph
  rhs  : List (RuleTerm R)

/-- A rule is valid if every graph term in it is a valid rule graph. -/
def Rule.valid {R : Type} (r : Rule R) : Bool :=
  r.lhs.validRuleGraph &&
  r.rhs.all (fun t => t.graph.validRuleGraph)

/-- Find a named rule in a finite rule table. -/
def lookupRule {R : Type} (rules : List (Rule R)) (name : String) : Option (Rule R) :=
  rules.find? (fun r => r.name == name)
