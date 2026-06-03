import Lean

open Lean

-- ============================================================
-- Structures
-- ============================================================

/-- A dart-map occurrence: ordered (source, target) dart pairs. -/
structure Occurrence where
  dartMap : Array (Nat × Nat)

/-- One term in a linear combination.
    All three payload fields are kept as raw `Json` so this file
    stays independent of the graph and coefficient representations. -/
structure LCTerm where
  coefficient : Json
  graph       : Json
  metadata    : Json

/-- A linear combination: a finite array of `Term`s. -/
structure LinearCombination where
  terms : Array LCTerm

/-- A single reduction step decoded from the certificate. -/
structure Step where
  termIndex  : Nat
  rule       : String
  occurrence : Occurrence
  after      : LinearCombination   -- was Json

/-- The top-level source-reduction certificate. -/
structure Certificate where
  format  : String
  version : Nat
  initial : Json
  steps   : Array Step   -- was Array Json
  final   : Json

-- ============================================================
-- JSON helpers  (unchanged)
-- ============================================================

-- `Json.getObjVal?` looks up a key in a JSON object and returns
-- `Except String Json`.  We wrap it to customise the error message.
def getObjVal (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | Except.ok v    => Except.ok v
  | Except.error _ => Except.error s!"missing key: {k}"

-- `Json.getStr?` returns `Except String String`.
def asString (j : Json) : Except String String :=
  match j.getStr? with
  | Except.ok s    => Except.ok s
  | Except.error _ => Except.error "expected string"

-- `Json.getNat?` returns `Except String Nat`.
def asNat (j : Json) : Except String Nat :=
  match j.getNat? with
  | Except.ok n    => Except.ok n
  | Except.error _ => Except.error "expected Nat"

-- `Json.getArr?` returns `Except String (Array Json)`.
def asArray (j : Json) : Except String (Array Json) :=
  match j.getArr? with
  | Except.ok a    => Except.ok a
  | Except.error _ => Except.error "expected array"

-- ============================================================
-- New helper
-- ============================================================

/-- Safe positional element access with a readable error.
    `Array.get? i` returns `Option Json`; we convert to `Except`. -/
def getElem (arr : Array Json) (i : Nat) : Except String Json :=
  match arr[i]? with
  | some v => .ok v
  | none   => .error s!"index {i} out of range (array size {arr.size})"
-- ============================================================
-- Decoders
-- ============================================================

/-- Decode one dart-pair from a two-element JSON array `[a, b]`. -/
def decodePair (j : Json) : Except String (Nat × Nat) := do
  let arr ← asArray j
  if arr.size ≠ 2 then
    throw s!"dart-map entry must be [a, b], got array of size {arr.size}"
  let a ← asNat (← getElem arr 0)
  let b ← asNat (← getElem arr 1)
  return (a, b)

/-- Decode an `Occurrence` from `{ "dartMap": [[a1,b1], [a2,b2], ...] }`.

    `Array.mapM` sequences the per-element decoder over the dart-pair array,
    collecting results into `Except String (Array (Nat × Nat))`. -/
def decodeOccurrence (j : Json) : Except String Occurrence := do
  let rawPairs ← asArray (← getObjVal j "dart_map")
  let dartMap  ← rawPairs.mapM decodePair
  return { dartMap }

/-- Decode one `Term` from a JSON object with `coefficient`, `graph`,
    and `metadata` fields.  All three values are stored as raw `Json`. -/
def decodeLCTerm (j : Json) : Except String LCTerm := do
  let coefficient ← getObjVal j "coefficient"
  let graph       ← getObjVal j "graph"
  let metadata    ← getObjVal j "metadata"
  return { coefficient, graph, metadata }

/-- Decode a `LinearCombination` from `{ "terms": [ ... ] }`.
    `Array.mapM decodeLCTerm` sequences the per-element decoder,
    short-circuiting on the first error. -/
def decodeLinearCombination (j : Json) : Except String LinearCombination := do
  let rawTerms ← asArray (← getObjVal j "terms")
  let terms    ← rawTerms.mapM decodeLCTerm
  return { terms }

/-- Decode a `Step` from a JSON object. -/
def decodeStep (j : Json) : Except String Step := do
  let termIndex  ← asNat    (← getObjVal j "term_index")
  let rule       ← asString (← getObjVal j "rule")
  let occurrence ← decodeOccurrence (← getObjVal j "occurrence")
  let after      ← decodeLinearCombination (← getObjVal j "after")
  return { termIndex, rule, occurrence, after }

/-- Decode the top-level certificate.
    `steps` is now decoded into `Array Step` via `Array.mapM decodeStep`. -/
def decodeCertificate (j : Json) : Except String Certificate := do
  let format   ← asString (← getObjVal j "format")
  let version  ← asNat    (← getObjVal j "version")
  let initial  ← getObjVal j "initial"
  let rawSteps ← asArray  (← getObjVal j "steps")
  let steps    ← rawSteps.mapM decodeStep
  let final    ← getObjVal j "final"
  return { format, version, initial, steps, final }

-- ============================================================
-- Entry point
-- ============================================================

/-- Read, decode, and print a summary of a certificate JSON file. -/
def readCertificate (path : System.FilePath) : IO Unit := do
  let text ← IO.FS.readFile path
  match Json.parse text >>= decodeCertificate with
  | Except.ok cert =>
      IO.println s!"format: {cert.format}"
      IO.println s!"version: {cert.version}"
      IO.println s!"steps: {cert.steps.size}"
      -- Print first step using Array.get? which returns Option Step.
      match cert.steps[0]? with
      | some step =>
          IO.println s!"first term index: {step.termIndex}"
          IO.println s!"first rule: {step.rule}"
          IO.println s!"first after terms: {step.after.terms.size}"
      | none =>
          IO.println "(no steps)"
  | Except.error e =>
      IO.eprintln s!"JSON error: {e}"
