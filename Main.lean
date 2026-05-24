
import

structure DartGraph where
  darts : List Nat
  partner : Nat → Nat
  vertex : Nat → Nat

  boundary : List Nat

structure Occurrence where
  dartMap : Nat → Nat
  vertexMap : Nat → Nat
  preservesIncidence : ∀ d, dartMap (partner d) = dartMap (partner (dartMap d))
  preservesPairings : ∀ d, partner (dartMap d) = partner (dartMap (partner d))
  preservesBoundary : ∀ b, vertexMap (boundary b) = vertexMap (boundary b)

  preservesDarts : ∀ d, dartMap d ∈ darts
  preservesVertices : ∀ v, vertexMap v ∈ vertex
  preservesBoundary : ∀ b, vertexMap (boundary b) = vertexMap (boundary b)

def preservesPartner
    (G H : DartGraph)
    (f : Nat → Nat) : Bool :=
  true

def preservesDartMap
    (G H : DartGraph)
    (f : Nat → Nat) : Bool :=
  true

def preservesVertexMap
    (G H : DartGraph)
    (f : Nat → Nat) : Bool :=
  true

def preservesBoundary
    (G H : DartGraph)
    (f : Nat → Nat) : Bool :=
  true

theorem checkDartGraph_sound :
  checkDartGraph_sound ... = true →
  validDartGraph ...
  := by
  intro h
  rw [checkOccurrence] at h
  exact h

theorem checkOccurrence_complete :
  validOccurrence ... →
  checkOccurrence ... = true
  := by
  intro h
