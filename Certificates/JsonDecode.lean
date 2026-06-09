import Lean
import Certificates.RawClosedGraph

open Lean

-- ============================================================
-- Structures (V2 schema)
-- ============================================================

/-- Decoded certificate occurrence: (source-dart, target-dart) pairs from a
    JSON object `{"k": v, ...}` (V2 format, replacing V1 array-of-pairs).
    Named `OccurrenceData` to avoid shadowing the graph-theoretic `Occurrence`
    from `Certificates.Graphs`. -/
structure OccurrenceData where
  dartMap : Array (Nat × Nat)

/-- A polynomial coefficient: array of string-encoded values. -/
structure Coefficient where
  coefficients : Array String

/-- One term in a linear combination.  V2: no `metadata` field. -/
structure LCTerm where
  coefficient : Coefficient
  graph       : RawClosedGraph

/-- A linear combination: a finite array of LCTerms. -/
structure LinearCombination where
  terms : Array LCTerm

/-- A dart-and-vertex bijection map, used for complement isomorphisms
    and relabellings.  Both maps are JSON objects `{"k": v, ...}` in V2. -/
structure DartVertexMap where
  dartMap   : Array (Nat × Nat)
  vertexMap : Array (Nat × Nat)

/-- Faithfully decoded `raw_dart_graph` from a V2 certificate.

    Unlike `closed_dart_graph`, dart and vertex labels are explicit and
    may be non-consecutive.  `vertexOf` and `partner` are stored as
    (dart-label, target-label) pairs decoded from JSON objects; no
    renumbering or validation is performed here. -/
structure RawDartGraph where
  darts    : Array Nat
  vertices : Array Nat
  vertexOf : Array (Nat × Nat)   -- dart label → vertex label
  partner  : Array (Nat × Nat)   -- dart label → partner dart label

/-- A single replacement certificate inside a reduction step. -/
structure ReplacementCertificate where
  coefficient           : Coefficient
  beforeGraph           : RawClosedGraph
  beforeOccurrence      : OccurrenceData
  afterRaw              : RawDartGraph
  afterOccurrence       : OccurrenceData
  complementIsomorphism : DartVertexMap
  relabelling           : DartVertexMap
  afterGraph            : RawClosedGraph

/-- A single reduction step.
    V2: adds `replacementCertificates`; `occurrence` uses object-format dart_map. -/
structure Step where
  termIndex               : Nat
  rule                    : String
  occurrence              : OccurrenceData
  replacementCertificates : Array ReplacementCertificate
  after                   : LinearCombination

/-- The top-level source-reduction certificate.
    V2: no `final` field; `initial` is a LinearCombination; adds `sourceKey`. -/
structure Certificate where
  format    : String
  version   : Nat
  sourceKey : String           -- new in V2
  initial   : LinearCombination
  steps     : Array Step

-- ============================================================
-- JSON helpers (unchanged)
-- ============================================================

-- Wrap Json.getObjVal? with a clearer error message.
def getObjVal (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | Except.ok v    => Except.ok v
  | Except.error _ => Except.error s!"missing key: {k}"

def asString (j : Json) : Except String String :=
  match j.getStr? with
  | Except.ok s    => Except.ok s
  | Except.error _ => Except.error "expected string"

def asNat (j : Json) : Except String Nat :=
  match j.getNat? with
  | Except.ok n    => Except.ok n
  | Except.error _ => Except.error "expected Nat"

def asArray (j : Json) : Except String (Array Json) :=
  match j.getArr? with
  | Except.ok a    => Except.ok a
  | Except.error _ => Except.error "expected array"

def getElem (arr : Array Json) (i : Nat) : Except String Json :=
  match arr[i]? with
  | some v => .ok v
  | none   => .error s!"index {i} out of range (array size {arr.size})"

-- ============================================================
-- New helpers for V2 object-format maps
-- ============================================================

/-- Parse a decimal string to a Nat.
    Used for the string keys in V2 dart_map / vertex_map objects. -/
def parseNat (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none   => .error s!"expected decimal integer key, got '{s}'"

/-- Decode a JSON object `{"k1": v1, "k2": v2, ...}` where every key is a
    decimal Nat string and every value is a Nat.  Returns (key, value) pairs.

    V2 uses this format for dart_map, vertex_map, occurrence.dart_map, etc.
    `Json.obj` stores its entries in an `RBMap String Json`; we fold over it
    to collect all pairs monadically. -/
def decodeNatMap (j : Json) : Except String (Array (Nat × Nat)) := do
  match j with
  | .obj m =>
    -- Collect raw (String × Json) pairs using RBMap.foldl, then decode.
    let rawPairs : List (String × Json) :=
      m.foldl (fun acc k v => (k, v) :: acc) []
    let pairs ← rawPairs.mapM fun (k, v) => do
      let ki ← parseNat k
      let vi ← asNat v
      return (ki, vi)
    return pairs.toArray
  | _ => throw "expected a JSON object for nat map"

-- ============================================================
-- Decoders
-- ============================================================

/-- Decode a V2 `closed_dart_graph` object into a `RawClosedGraph`.

    The V2 format uses consecutive implicit dart labels 0..num_darts-1 and
    vertex labels 0..num_vertices-1.  `vertex_of` and `partner` are positional
    arrays already in the `RawClosedGraph` layout, so we just construct the
    explicit label ranges and pass the arrays through. -/
def decodeClosedDartGraph (j : Json) : Except String RawClosedGraph := do
  let fmt ← asString (← getObjVal j "format"
    |>.mapError (fun e => s!"decodeClosedDartGraph: {e}\nJSON: {j.compress}"))
  if fmt ≠ "closed_dart_graph" then
    throw s!"expected closed_dart_graph, got '{fmt}'"
  let numDarts    ← asNat (← getObjVal j "num_darts")
  let numVertices ← asNat (← getObjVal j "num_vertices")
  let vertexOf    ← (← asArray (← getObjVal j "vertex_of")).mapM asNat
  let partner     ← (← asArray (← getObjVal j "partner")).mapM asNat
  -- Consecutive labels: darts are 0..numDarts-1, vertices 0..numVertices-1.
  let darts    : Array Nat := (List.range numDarts).toArray
  let vertices : Array Nat := (List.range numVertices).toArray
  return { darts, vertices, vertexOf, partner }

/-- Decode a V2 `raw_dart_graph` object into a `RawDartGraph`.

    Dart and vertex labels are read as-is from the explicit arrays.
    `vertex_of` and `partner` are JSON objects decoded via `decodeNatMap`,
    producing (dart-label, target-label) pairs.  No renumbering, no
    consecutive-numbering assumption, no validation. -/
def decodeRawDartGraph (j : Json) : Except String RawDartGraph := do
  let fmt ← asString (← getObjVal j "format"
    |>.mapError (fun e => s!"decodeRawDartGraph: {e}\nJSON: {j.compress}"))
  if fmt ≠ "raw_dart_graph" then
    throw s!"expected raw_dart_graph, got '{fmt}'"
  let darts    ← (← asArray (← getObjVal j "darts")).mapM asNat
  let vertices ← (← asArray (← getObjVal j "vertices")).mapM asNat
  let vertexOf ← decodeNatMap (← getObjVal j "vertex_of")
  let partner  ← decodeNatMap (← getObjVal j "partner")
  return { darts, vertices, vertexOf, partner }

/-- Decode a `Coefficient` from `{ "coefficients": ["...", ...] }`. -/
def decodeCoefficient (j : Json) : Except String Coefficient := do
  let rawArr       ← asArray (← getObjVal j "coefficients")
  let coefficients ← rawArr.mapM asString
  return { coefficients }

/-- Decode an `OccurrenceData` from `{ "dart_map": {"k": v, ...} }`.
    V2: dart_map is a JSON object, not an array of pairs. -/
def decodeOccurrence (j : Json) : Except String OccurrenceData := do
  let dartMap ← decodeNatMap (← getObjVal j "dart_map")
  return { dartMap }

/-- Decode one `LCTerm`.  V2: no `metadata` field; `graph` is a closed_dart_graph. -/
def decodeLCTerm (j : Json) : Except String LCTerm := do
  let coefficient ← decodeCoefficient (← getObjVal j "coefficient")
  let graph       ← decodeClosedDartGraph (← getObjVal j "graph")
  return { coefficient, graph }

/-- Decode a `LinearCombination` from `{ "terms": [ ... ] }`. -/
def decodeLinearCombination (j : Json) : Except String LinearCombination := do
  let rawTerms ← asArray (← getObjVal j "terms")
  let terms    ← rawTerms.mapM decodeLCTerm
  return { terms }

/-- Decode a `DartVertexMap` from an object with `dart_map` and `vertex_map`.
    Both are JSON objects in V2. -/
def decodeDartVertexMap (j : Json) : Except String DartVertexMap := do
  let dartMap   ← decodeNatMap (← getObjVal j "dart_map")
  let vertexMap ← decodeNatMap (← getObjVal j "vertex_map")
  return { dartMap, vertexMap }

/-- Decode one `ReplacementCertificate`.
    `before_graph` and `after_graph` are decoded as `RawClosedGraph`.
    `after_raw` (raw_dart_graph format) stays as raw Json for now. -/
def decodeReplacementCertificate (j : Json) : Except String ReplacementCertificate := do
  let coefficient           ← decodeCoefficient   (← getObjVal j "coefficient")
  let beforeGraph           ← decodeClosedDartGraph (← getObjVal j "before_graph")
  let beforeOccurrence      ← decodeOccurrence    (← getObjVal j "before_occurrence")
  let afterRaw              ← decodeRawDartGraph (← getObjVal j "after_raw")
  let afterOccurrence       ← decodeOccurrence    (← getObjVal j "after_occurrence")
  let complementIsomorphism ← decodeDartVertexMap (← getObjVal j "complement_isomorphism")
  let relabelling           ← decodeDartVertexMap (← getObjVal j "relabelling")
  let afterGraph            ← decodeClosedDartGraph (← getObjVal j "after_graph")
  return { coefficient, beforeGraph, beforeOccurrence, afterRaw,
           afterOccurrence, complementIsomorphism, relabelling, afterGraph }

/-- Decode a `Step` from a JSON object.
    V2: adds `replacement_certificates`; `occurrence` uses object-format dart_map. -/
def decodeStep (j : Json) : Except String Step := do
  let termIndex               ← asNat    (← getObjVal j "term_index")
  let rule                    ← asString (← getObjVal j "rule")
  let occurrence              ← decodeOccurrence (← getObjVal j "occurrence")
  let rawReplCerts            ← asArray  (← getObjVal j "replacement_certificates")
  let replacementCertificates ← rawReplCerts.mapM decodeReplacementCertificate
  let after                   ← decodeLinearCombination (← getObjVal j "after")
  return { termIndex, rule, occurrence, replacementCertificates, after }

/-- Decode the top-level V2 certificate.
    V2: `initial` is a LinearCombination; `source_key` is present; no `final`. -/
def decodeCertificate (j : Json) : Except String Certificate := do
  let format ← asString (← getObjVal j "format"
    |>.mapError (fun e => s!"decodeCertificate: {e}\nJSON: {j.compress}"))
  let version   ← asNat    (← getObjVal j "version")
  let sourceKey ← asString (← getObjVal j "source_key")
  let initial   ← decodeLinearCombination (← getObjVal j "initial")
  let rawSteps  ← asArray  (← getObjVal j "steps")
  let steps     ← rawSteps.mapM decodeStep
  return { format, version, sourceKey, initial, steps }

-- ============================================================
-- Entry point
-- ============================================================

/-- Read, decode, and print a summary of a V2 certificate JSON file. -/
def readCertificate (path : System.FilePath) : IO Unit := do
  let text ← IO.FS.readFile path
  match Json.parse text >>= decodeCertificate with
  | Except.ok cert =>
      IO.println s!"format: {cert.format}"
      IO.println s!"version: {cert.version}"
      IO.println s!"source_key: {cert.sourceKey}"
      IO.println s!"initial terms: {cert.initial.terms.size}"
      match cert.initial.terms[0]? with
      | some t  => IO.println s!"initial[0] graph darts: {t.graph.darts.size}"
      | none    => pure ()
      IO.println s!"steps: {cert.steps.size}"
      match cert.steps[0]? with
      | some step =>
          IO.println s!"first term_index: {step.termIndex}"
          IO.println s!"first rule: {step.rule}"
          IO.println s!"first replacement_certificates: {step.replacementCertificates.size}"
          IO.println s!"first after terms: {step.after.terms.size}"
          match step.after.terms[0]? with
          | some term =>
              let cs  := term.coefficient.coefficients.toList
              let cStr := String.intercalate ", " cs
              IO.println s!"first after[0] coefficient: {cStr}"
          | none =>
              IO.println "(first after has no terms)"
      | none =>
          IO.println "(no steps)"
  | Except.error e =>
      IO.eprintln s!"JSON error: {e}"
