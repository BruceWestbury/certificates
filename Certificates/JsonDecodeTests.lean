import Certificates.JsonDecode
import Certificates.LCChecker

open Lean

/-!
# V2 decoder + graph smoke tests

Two levels of checking:

**Level 1 — decoder** (`smokeTestCertificate` shallow section):
  top-level fields, non-empty initial/steps, replacement certificate shapes.

**Level 2 — graph validity** (`validateGraphsInCert`):
  every `RawClosedGraph` in the certificate is checked via
  `RawClosedGraph.validate` (involution, no fixed points, label range, sizes)
  plus a local valence-3 check (not in `validate`).

`afterRaw` (raw_dart_graph) is NOT validated here.
Occurrences, complements, and substitutions are NOT checked here.
-/

-- ════════════════════════════════════════════════════════════
-- Shared helpers
-- ════════════════════════════════════════════════════════════

private def check (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println s!"  [pass] {label}"
  else       IO.println s!"  [FAIL] {label}"

-- ════════════════════════════════════════════════════════════
-- Graph-validity helpers
-- ════════════════════════════════════════════════════════════

/-- True iff every vertex label in `g.vertices` has exactly 3 incident darts.

    `RawClosedGraph.validate` does not check valence, so we add it here.
    The V2 closed_dart_graph format uses consecutive labels, so
    `g.vertexOf.filter (· == v)` counts darts incident to vertex `v`. -/
private def allValence3 (g : RawClosedGraph) : Bool :=
  g.vertices.all fun v => (g.vertexOf.filter (· == v)).size == 3

/-- Run structural checks only (no valence check).
    Used for **source graphs** (`initial`, `beforeGraph`) which contain
    exactly one 4-valent vertex by design; valence-3 is intentionally absent. -/
private def checkStructural (g : RawClosedGraph) : Option String :=
  match g.validate with
  | .error e => some e
  | .ok _    => none

/-- Run structural checks **and** verify every vertex has valence 3.
    Used for **result graphs** (`afterGraph`, `step.after.terms`) which must
    be fully trivalent. -/
private def checkTrivalent (g : RawClosedGraph) : Option String :=
  match g.validate with
  | .error e => some e
  | .ok _    =>
    if !allValence3 g then some "not all vertices have valence 3"
    else none

/-- Validate one labelled collection of `RawClosedGraph` objects.
    `checker` selects which checks to apply (structural-only or +valence-3).
    Prints a one-line failure message per bad graph; silent on success.
    Returns `(checked, failed)`. -/
private def validateCollection
    (categoryLabel : String)
    (checker : RawClosedGraph → Option String)
    (graphs : Array (String × RawClosedGraph)) : IO (Nat × Nat) := do
  let mut checked := 0
  let mut failed  := 0
  for (graphLabel, g) in graphs do
    checked := checked + 1
    match checker g with
    | none     => pure ()   -- silent on success
    | some msg =>
      IO.println s!"    [FAIL] {categoryLabel} {graphLabel} ({g.darts.size} darts): {msg}"
      failed := failed + 1
  return (checked, failed)

-- ════════════════════════════════════════════════════════
-- RawDartGraph validation
-- ════════════════════════════════════════════════════════

-- Local helpers (the analogues in RawClosedGraph.lean are private there).
private def rdgContains (xs : Array Nat) (x : Nat) : Bool := xs.any (· == x)

private def rdgHasDups (xs : Array Nat) : Bool :=
  Id.run do
    for i in List.range xs.size do
      for j in List.range i do
        if xs[i]! == xs[j]! then return true
    return false

/-- Find the value associated with `key` in a (key, value) pair array. -/
private def rdgLookup (pairs : Array (Nat × Nat)) (key : Nat) : Option Nat :=
  Id.run do
    for p in pairs do
      if p.1 == key then return some p.2
    return none

/-- Structural validation for `RawDartGraph`.

    Checks dart/vertex label integrity, complete coverage of both maps,
    partner involution, and absence of fixed points.
    Does **not** require trivalence, consecutive labels, or connectivity.

    Returns `Except.ok ()` on success, `Except.error msg` on the first failure. -/
def validateRawDartGraph (g : RawDartGraph) : Except String Unit := do
  -- (1) Dart labels are distinct.
  if rdgHasDups g.darts then
    throw "darts contains duplicate labels"
  -- (2) Vertex labels are distinct.
  if rdgHasDups g.vertices then
    throw "vertices contains duplicate labels"
  -- (3) Every vertexOf key is a dart label; every vertexOf value is a vertex label.
  for p in g.vertexOf do
    if !rdgContains g.darts p.1    then throw s!"vertexOf key {p.1} is not a dart label"
    if !rdgContains g.vertices p.2 then throw s!"vertexOf({p.1}) = {p.2} is not a vertex label"
  -- (4) Every partner key and value is a dart label.
  for p in g.partner do
    if !rdgContains g.darts p.1 then throw s!"partner key {p.1} is not a dart label"
    if !rdgContains g.darts p.2 then throw s!"partner({p.1}) = {p.2} is not a dart label"
  -- (5) Functional completeness: vertexOf covers every dart exactly once.
  --     Size match + coverage (check 3) + dart coverage = exact bijection.
  if g.vertexOf.size ≠ g.darts.size then
    throw s!"vertexOf has {g.vertexOf.size} entries but darts has {g.darts.size}"
  for d in g.darts do
    if (rdgLookup g.vertexOf d).isNone then
      throw s!"dart {d} has no vertexOf entry"
  -- (6) Functional completeness: partner covers every dart exactly once.
  if g.partner.size ≠ g.darts.size then
    throw s!"partner has {g.partner.size} entries but darts has {g.darts.size}"
  for d in g.darts do
    if (rdgLookup g.partner d).isNone then
      throw s!"dart {d} has no partner entry"
  -- (7) Partner is an involution: partner(partner(d)) = d.
  for d in g.darts do
    match rdgLookup g.partner d with
    | none   => pure ()   -- unreachable after check (6)
    | some e =>
      match rdgLookup g.partner e with
      | none    => throw s!"partner({d}) = {e} has no partner entry (involution broken)"
      | some dd =>
        if dd ≠ d then
          throw s!"partner not involution: partner(partner({d})) = {dd} ≠ {d}"
  -- (8) No fixed points: partner(d) ≠ d.
  for d in g.darts do
    match rdgLookup g.partner d with
    | none   => pure ()
    | some e =>
      if e == d then throw s!"partner has a fixed point at dart {d}"
  -- (9) Every vertex has at least one incident dart.
  for v in g.vertices do
    if !g.vertexOf.any (fun p => p.2 == v) then
      throw s!"vertex {v} has no incident dart"

-- ════════════════════════════════════════════════════════
-- Relabelling check
-- ════════════════════════════════════════════════════════

/-- Verify that `mapArr` is a surjective injection from a subset of `srcSet`
    onto all of `dstSet`.  Keys are `srcSet` elements; values cover exactly
    `dstSet`.  Surjectivity is required; the key set may be a proper subset
    of `srcSet` (afterRaw may have more darts than afterGraph).
    Returns `Except.error` with the first violation found. -/
private def checkPartialSurjectionExn
    (srcSet dstSet : Array Nat)
    (mapArr : Array (Nat × Nat))
    (name : String) : Except String Unit := do
  -- |rel| = |dstSet|: the map hits all target elements exactly once.
  if mapArr.size ≠ dstSet.size then
    throw s!"{name}: map has {mapArr.size} entries but target has {dstSet.size} elements"
  -- Every key is in srcSet; every value is in dstSet.
  for p in mapArr do
    if !rdgContains srcSet p.1 then throw s!"{name}: key {p.1} not in source set"
    if !rdgContains dstSet p.2 then throw s!"{name}: value {p.2} not in target set"
  -- Surjective: every target element has a preimage.
  for t in dstSet do
    if !(mapArr.any fun p => p.2 == t) then
      throw s!"{name}: target element {t} has no preimage"
  -- Injective: no duplicate values (and no duplicate keys from JSON).
  if rdgHasDups (mapArr.map (·.2)) then
    throw s!"{name}: not injective (duplicate values)"
  if rdgHasDups (mapArr.map (·.1)) then
    throw s!"{name}: duplicate keys"

/-- Check that `rel` is a valid relabelling from a subset of `raw` (afterRaw)
    surjectively onto `closed` (afterGraph).

    Direction: `rel.dartMap` keys are raw dart labels; values are closed dart
    labels.  `raw` may have MORE darts than `closed` (afterRaw is a
    pre-canonical intermediate); the uncovered raw darts are complement darts
    handled elsewhere.

    Conditions checked here:
    1. `rel.dartMap`   covers all of `closed.darts`    injectively from a subset of `raw.darts`.
    2. `rel.vertexMap` covers all of `closed.vertices` injectively from a subset of `raw.vertices`.
    3. Incidence: `rel.vertexMap(raw.vertexOf(d)) = closed.vertexOf[d']`
       for every `(d, d')` in `rel.dartMap`.
    4. Pairing: `rel.dartMap(raw.partner(d)) = closed.partner[d']`
       for every `(d, d')` in `rel.dartMap`. -/
def checkRelabelling
    (raw    : RawDartGraph)
    (rel    : DartVertexMap)
    (closed : RawClosedGraph) : Except String Unit := do
  -- (1) dart map: subset of raw.darts → (surjection onto) closed.darts.
  checkPartialSurjectionExn raw.darts closed.darts rel.dartMap "dart map"
  -- (2) vertex map: subset of raw.vertices → (surjection onto) closed.vertices.
  checkPartialSurjectionExn raw.vertices closed.vertices rel.vertexMap "vertex map"
  -- (3) Incidence: for each (d, d') in rel.dartMap,
  --     rel.vertexMap(raw.vertexOf(d)) = closed.vertexOf[d'].
  for p in rel.dartMap do
    let d  := p.1   -- raw dart label
    let d' := p.2   -- closed dart label (consecutive, = array index)
    match rdgLookup raw.vertexOf d with
    | none => throw s!"raw.vertexOf({d}) missing"
    | some rawV =>
      match rdgLookup rel.vertexMap rawV with
      | none => throw s!"rel.vertexMap({rawV}) missing"
      | some mappedV =>
        match closed.vertexOf[d']? with
        | none    => throw s!"closed.vertexOf[{d'}] out of range"
        | some cv =>
          if cv ≠ mappedV then
            throw s!"incidence at raw dart {d}: rel.vertexMap(raw.vertexOf({d})) = {mappedV} ≠ closed.vertexOf[{d'}] = {cv}"
  -- (4) Pairing: for each (d, d') in rel.dartMap, when raw.partner(d) is
  --     also in rel.dartMap, check rel.dartMap(raw.partner(d)) = closed.partner[d'].
  --     If raw.partner(d) is not in rel.dartMap, it is a complement dart;
  --     that pairing is certified by the complement isomorphism, not here.
  for p in rel.dartMap do
    let d  := p.1
    let d' := p.2
    match rdgLookup raw.partner d with
    | none => throw s!"raw.partner({d}) missing"
    | some rawE =>
      match rdgLookup rel.dartMap rawE with
      | none  => pure ()   -- rawE is a complement dart; skip
      | some e' =>
        match closed.partner[d']? with
        | none    => throw s!"closed.partner[{d'}] out of range"
        | some cp =>
          if cp ≠ e' then
            throw s!"partner at raw dart {d}: rel(raw.partner({d})) = {e'} ≠ closed.partner[{d'}] = {cp}"

-- ════════════════════════════════════════════════════════
-- Graph validation across a full certificate
-- ════════════════════════════════════════════════════════════

/-- Validate every `RawClosedGraph` in `cert`.
    Covers initial terms, step-after terms, replacement beforeGraph/afterGraph.
    Prints counts and [pass]/[FAIL] per category. -/
private def validateGraphsInCert (cert : Certificate) : IO Unit := do
  IO.println "  --- graph validation ---"

  -- 1. Initial terms  — source graphs, one 4-valent vertex expected: structural only
  let initialGraphs : Array (String × RawClosedGraph) :=
    cert.initial.terms.mapIdx fun i t => (s!"initial[{i}]", t.graph)
  let (nInit, failInit) ← validateCollection "initial" checkStructural initialGraphs
  IO.println s!"  initial-term graphs:        {nInit} checked (structural, no valence-3)"
  check s!"all {nInit} initial graphs structurally valid" (failInit == 0)

  -- 2. Step-after terms  — result graphs, must be trivalent
  let mut afterGraphs : Array (String × RawClosedGraph) := #[]
  let mut si := 0
  for step in cert.steps do
    let mut ti := 0
    for t in step.after.terms do
      afterGraphs := afterGraphs.push (s!"step[{si}].after[{ti}]", t.graph)
      ti := ti + 1
    si := si + 1
  let (nAfter, failAfter) ← validateCollection "after" checkTrivalent afterGraphs
  IO.println s!"  step-after-term graphs:     {nAfter} checked (structural + valence-3)"
  check s!"all {nAfter} after-term graphs trivalent" (failAfter == 0)

  -- 3. Replacement beforeGraph  — source graphs, structural only
  let mut beforeGraphs : Array (String × RawClosedGraph) := #[]
  si := 0
  for step in cert.steps do
    let mut ri := 0
    for rc in step.replacementCertificates do
      beforeGraphs := beforeGraphs.push (s!"step[{si}].rc[{ri}].before", rc.beforeGraph)
      ri := ri + 1
    si := si + 1
  let (nBefore, failBefore) ← validateCollection "before" checkStructural beforeGraphs
  IO.println s!"  replacement beforeGraphs:   {nBefore} checked (structural, no valence-3)"
  check s!"all {nBefore} beforeGraphs structurally valid" (failBefore == 0)

  -- 4. Replacement afterGraph  — result graphs, must be trivalent
  let mut afterReplGraphs : Array (String × RawClosedGraph) := #[]
  si := 0
  for step in cert.steps do
    let mut ri := 0
    for rc in step.replacementCertificates do
      afterReplGraphs := afterReplGraphs.push (s!"step[{si}].rc[{ri}].after", rc.afterGraph)
      ri := ri + 1
    si := si + 1
  let (nAfterG, failAfterG) ← validateCollection "afterGraph" checkTrivalent afterReplGraphs
  IO.println s!"  replacement afterGraphs:    {nAfterG} checked (structural + valence-3)"
  check s!"all {nAfterG} afterGraphs trivalent" (failAfterG == 0)

  -- 5. Replacement afterRaw  — raw_dart_graph, validate structure
  let mut afterRawGraphs : Array (String × RawDartGraph) := #[]
  si := 0
  for step in cert.steps do
    let mut ri := 0
    for rc in step.replacementCertificates do
      afterRawGraphs := afterRawGraphs.push (s!"step[{si}].rc[{ri}].afterRaw", rc.afterRaw)
      ri := ri + 1
    si := si + 1
  let mut nRaw := 0
  let mut failRaw := 0
  for (graphLabel, g) in afterRawGraphs do
    nRaw := nRaw + 1
    match validateRawDartGraph g with
    | .ok _    => pure ()
    | .error e =>
      IO.println s!"    [FAIL] afterRaw {graphLabel} ({g.darts.size} darts): {e}"
      failRaw := failRaw + 1
  IO.println s!"  afterRaw graphs:            {nRaw} checked"
  check s!"all {nRaw} afterRaw graphs structurally valid" (failRaw == 0)

  -- 6. Relabelling: afterRaw → afterGraph
  IO.println "  --- relabelling check ---"
  let mut nRel := 0
  let mut failRel := 0
  si := 0
  for step in cert.steps do
    let mut ri := 0
    for rc in step.replacementCertificates do
      nRel := nRel + 1
      match checkRelabelling rc.afterRaw rc.relabelling rc.afterGraph with
      | .ok _    => pure ()
      | .error e =>
        IO.println s!"    [FAIL] step[{si}].rc[{ri}]: {e}"
        failRel := failRel + 1
      ri := ri + 1
    si := si + 1
  IO.println s!"  relabellings:               {nRel} checked"
  check s!"all {nRel} relabellings valid" (failRel == 0)

  -- Summary
  let closedFail := failInit + failAfter + failBefore + failAfterG
  let closedTotal := nInit + nAfter + nBefore + nAfterG
  IO.println s!"  closed graphs: {closedTotal - closedFail} passed, {closedFail} failed"
  IO.println s!"  raw graphs:    {nRaw - failRaw} passed, {failRaw} failed"
  IO.println s!"  relabellings:  {nRel - failRel} passed, {failRel} failed"

-- ════════════════════════════════════════════════════════════
-- Smoke test (decoder + graph validity)
-- ════════════════════════════════════════════════════════════

/-- Read and decode one V2 certificate, run shallow decoder checks, then
    validate every `RawClosedGraph` in the certificate.
    On a decode error the exact message is printed and the function aborts. -/
def smokeTestCertificate (label : String) (path : System.FilePath) : IO Unit := do
  IO.println s!"=== {label}: {path} ==="
  let text ← IO.FS.readFile path
  match Json.parse text >>= decodeCertificate with
  | .error e =>
    IO.println s!"  [FAIL] decode error: {e}"
    IO.println s!"=== {label}: ABORTED ==="
  | .ok cert =>
    -- ── Level 1: decoder sanity ──────────────────────────────
    IO.println s!"  format:     {cert.format}"
    IO.println s!"  version:    {cert.version}"
    IO.println s!"  source_key: {cert.sourceKey}"
    check "format  = source_reduction_certificate" (cert.format  == "source_reduction_certificate")
    check "version = 2"                            (cert.version == 2)

    IO.println s!"  initial.terms: {cert.initial.terms.size}"
    check "initial has at least one term" (cert.initial.terms.size > 0)
    match cert.initial.terms[0]? with
    | none   => IO.println "  [FAIL] initial.terms[0] missing"
    | some t =>
      IO.println s!"  initial[0].graph: {t.graph.darts.size} darts, {t.graph.vertices.size} vertices"
      check "initial[0] graph has darts"    (t.graph.darts.size    > 0)
      check "initial[0] graph has vertices" (t.graph.vertices.size > 0)

    IO.println s!"  steps: {cert.steps.size}"
    check "certificate has steps" (cert.steps.size > 0)
    match cert.steps[0]? with
    | none      => IO.println "  [FAIL] steps[0] missing"
    | some step =>
      IO.println s!"  steps[0].rule:       {step.rule}"
      IO.println s!"  steps[0].occurrence: {step.occurrence.dartMap.size} dart-map entries"
      IO.println s!"  steps[0].replCerts:  {step.replacementCertificates.size}"
      IO.println s!"  steps[0].after:      {step.after.terms.size} terms"
      check "steps[0] has replacement certificates" (step.replacementCertificates.size > 0)
      check "steps[0].after has terms"              (step.after.terms.size             > 0)
      match step.replacementCertificates[0]? with
      | none    => IO.println "  [FAIL] replacementCertificates[0] missing"
      | some rc =>
        IO.println s!"  rc[0].beforeGraph:  {rc.beforeGraph.darts.size} darts"
        IO.println s!"  rc[0].afterRaw:     {rc.afterRaw.darts.size} darts (raw_dart_graph, not validated)"
        IO.println s!"  rc[0].afterGraph:   {rc.afterGraph.darts.size} darts"
        IO.println s!"  rc[0].isoMap:       {rc.complementIsomorphism.dartMap.size} dart entries"
        check "rc[0].beforeGraph has darts"            (rc.beforeGraph.darts.size             > 0)
        check "rc[0].afterGraph has darts"             (rc.afterGraph.darts.size              > 0)
        check "rc[0] complement isomorphism non-empty" (rc.complementIsomorphism.dartMap.size > 0)

    -- ── Level 2: graph validity ──────────────────────────────
    validateGraphsInCert cert

    IO.println s!"=== {label}: done ==="

-- ════════════════════════════════════════════════════════════
-- Run both certificates
-- ════════════════════════════════════════════════════════════

#eval smokeTestCertificate "F4"
        "../cubic-jordan/projects/f4/certificates/t10/sources_0000.json"

#eval smokeTestCertificate "E6"
        "../cubic-jordan/projects/e6/certificates/t14/sources_0000.json"

-- ════════════════════════════════════════════════════════
-- LC-checker smoke tests
-- ════════════════════════════════════════════════════════

private def lcCheck (label : String) (path : System.FilePath) : IO Unit := do
  IO.println s!"=== {label}: LC check ==="
  let text ← IO.FS.readFile path
  match Json.parse text >>= decodeCertificate with
  | .error e =>
    IO.println s!"  [FAIL] decode: {e}"
  | .ok cert =>
    IO.println s!"  steps to check: {cert.steps.size}"
    match checkAllSteps cert with
    | .error e =>
      IO.println s!"  [FAIL] LC arithmetic: {e}"
    | .ok _ ->
      IO.println s!"  [pass] all {cert.steps.size} LC steps valid"
  IO.println s!"=== {label}: LC done ==="

#eval lcCheck "F4" "../cubic-jordan/projects/f4/certificates/t10/sources_0000.json"
#eval lcCheck "E6" "../cubic-jordan/projects/e6/certificates/t14/sources_0000.json"
