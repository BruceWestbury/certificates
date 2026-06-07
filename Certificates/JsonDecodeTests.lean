import Certificates.JsonDecode

open Lean

/-!
# V2 decoder smoke tests

Runs `smokeTestCertificate` against real F4 and E6 certificate files.
Both use the same V2 schema; no theory-specific decoder code exists.

This is a **decoder-only** test: no graph well-formedness, no occurrence
validity, no substitution checks.

Paths are relative to the package root (where `lakefile.lean` lives),
which is the working directory used by `lake build` and `lake exe`.
-/

-- ── helper ────────────────────────────────────────────────────────────────────

private def check (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println s!"  [pass] {label}"
  else       IO.println s!"  [FAIL] {label}"

-- ── shared checking logic ─────────────────────────────────────────────────────

/-- Read and decode one V2 certificate, then print shallow sanity checks.
    Reports `[pass]` / `[FAIL]` for each structural expectation.
    On a decode error the exact message is printed and the test aborts. -/
def smokeTestCertificate (label : String) (path : System.FilePath) : IO Unit := do
  IO.println s!"=== {label}: {path} ==="
  let text ← IO.FS.readFile path
  match Json.parse text >>= decodeCertificate with
  | .error e =>
    IO.println s!"  [FAIL] decode error: {e}"
    IO.println s!"=== {label}: ABORTED ==="
  | .ok cert =>
    -- 1. Top-level fields
    IO.println s!"  format:     {cert.format}"
    IO.println s!"  version:    {cert.version}"
    IO.println s!"  source_key: {cert.sourceKey}"
    check "format  = source_reduction_certificate" (cert.format  == "source_reduction_certificate")
    check "version = 2"                            (cert.version == 2)

    -- 2. Initial linear combination
    IO.println s!"  initial.terms: {cert.initial.terms.size}"
    check "initial has at least one term" (cert.initial.terms.size > 0)
    match cert.initial.terms[0]? with
    | none   => IO.println "  [FAIL] initial.terms[0] missing"
    | some t =>
      IO.println s!"  initial[0].graph.darts:    {t.graph.darts.size}"
      IO.println s!"  initial[0].graph.vertices: {t.graph.vertices.size}"
      check "initial[0] graph has darts"    (t.graph.darts.size    > 0)
      check "initial[0] graph has vertices" (t.graph.vertices.size > 0)

    -- 3. Steps
    IO.println s!"  steps: {cert.steps.size}"
    check "certificate has steps" (cert.steps.size > 0)
    match cert.steps[0]? with
    | none      => IO.println "  [FAIL] steps[0] missing"
    | some step =>
      IO.println s!"  steps[0].rule:        {step.rule}"
      IO.println s!"  steps[0].occurrence:  {step.occurrence.dartMap.size} dart-map entries"
      IO.println s!"  steps[0].replCerts:   {step.replacementCertificates.size}"
      IO.println s!"  steps[0].after.terms: {step.after.terms.size}"
      check "steps[0] has replacement certificates" (step.replacementCertificates.size > 0)
      check "steps[0].after has terms"              (step.after.terms.size             > 0)

      -- 4. First replacement certificate
      match step.replacementCertificates[0]? with
      | none    => IO.println "  [FAIL] replacementCertificates[0] missing"
      | some rc =>
        IO.println s!"  rc[0].beforeGraph.darts:  {rc.beforeGraph.darts.size}"
        IO.println s!"  rc[0].afterRaw.darts:     {rc.afterRaw.darts.size}"
        IO.println s!"  rc[0].afterGraph.darts:   {rc.afterGraph.darts.size}"
        IO.println s!"  rc[0].isoMap entries:     {rc.complementIsomorphism.dartMap.size}"
        check "rc[0].beforeGraph has darts"            (rc.beforeGraph.darts.size              > 0)
        check "rc[0].afterRaw  has darts"              (rc.afterRaw.darts.size                 > 0)
        check "rc[0].afterGraph has darts"             (rc.afterGraph.darts.size               > 0)
        check "rc[0] complement isomorphism non-empty" (rc.complementIsomorphism.dartMap.size  > 0)

    IO.println s!"=== {label}: done ==="

-- ── run both certificates ─────────────────────────────────────────────────────

#eval smokeTestCertificate "F4"
        "../cubic-jordan/projects/f4/certificates/t10/sources_0000.json"

#eval smokeTestCertificate "E6"
        "../cubic-jordan/projects/e6/certificates/t14/sources_0000.json"
