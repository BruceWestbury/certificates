import Certificates.RawClosedGraph
import Certificates.ValidatedClosedGraph

/-!
# Tests for `RawClosedGraph.validate`

Each `#eval` prints `[ok]` or `[error] <message>`.
These are elaboration-time checks; the results appear in the build output.
-/

private def check (label : String) (result : Except String Unit) : IO Unit :=
  match result with
  | .ok _    => IO.println s!"[ok]    {label}"
  | .error e => IO.println s!"[error] {label} — {e}"

-- ── 1. Valid closed graph ────────────────────────────────────────────────────
-- Two darts with non-consecutive labels (10, 11) paired into one edge.
-- One vertex (label 0); both darts are incident to it.
#eval check "1. valid two-dart graph" <|
  RawClosedGraph.validate {
    darts    := #[10, 11]
    vertices := #[0]
    vertexOf := #[0,  0]   -- dart 10 → vertex 0,  dart 11 → vertex 0
    partner  := #[11, 10]  -- dart 10 ↔ dart 11
  }
-- Expected: [ok]    1. valid two-dart graph

-- ── 2. Duplicate dart label ──────────────────────────────────────────────────
-- Label 5 appears twice in darts.
#eval check "2. duplicate dart label" <|
  RawClosedGraph.validate {
    darts    := #[5, 5]
    vertices := #[0]
    vertexOf := #[0, 0]
    partner  := #[5, 5]
  }
-- Expected: [error] 2. duplicate dart label — darts contains duplicate labels

-- ── 3. Partner entry not a dart label ───────────────────────────────────────
-- partner[1] = 99, but 99 is not in darts.
#eval check "3. partner entry not a dart label" <|
  RawClosedGraph.validate {
    darts    := #[10, 11]
    vertices := #[0]
    vertexOf := #[0,  0]
    partner  := #[11, 99]  -- 99 is not a dart label
  }
-- Expected: [error] 3. partner entry not a dart label — partner[1] = 99 is not a dart label (dart 11)

-- ── 4. Partner not an involution ─────────────────────────────────────────────
-- partner encodes the 4-cycle 10→11→12→13→10, which is not an involution.
-- partner(partner(10)) = partner(11) = 12 ≠ 10.
#eval check "4. partner not an involution" <|
  RawClosedGraph.validate {
    darts    := #[10, 11, 12, 13]
    vertices := #[0]
    vertexOf := #[0,  0,  0,  0]
    partner  := #[11, 12, 13, 10]  -- 4-cycle, not an involution
  }
-- Expected: [error] 4. partner not an involution — partner not an involution: partner(partner(10)) = 12 ≠ 10

-- ── 5. Fixed point ───────────────────────────────────────────────────────────
-- Both darts map to themselves: partner(10) = 10 and partner(11) = 11.
-- The involution check passes (partner∘partner = id), but fixed points are rejected.
#eval check "5. fixed point" <|
  RawClosedGraph.validate {
    darts    := #[10, 11]
    vertices := #[0]
    vertexOf := #[0,  0]
    partner  := #[10, 11]  -- both darts are fixed points
  }
-- Expected: [error] 5. fixed point — partner has a fixed point at dart 10

#eval check "6. validates" <|
  RawClosedGraph.validate {
    darts    := #[10, 11]
    vertices := #[100]
    vertexOf := #[100, 100]
    partner  := #[11, 10]
  }
-- Expected: [ok] 6. validates

private def checkValidated (name : String) (r : Except String ValidatedClosedGraph) : IO Unit := do
  match r with
  | Except.ok v =>
      IO.println s!"[ok]    {name} — partnerIdx = {v.partnerIdx}, vertexIdx = {v.vertexIdx}"
  | Except.error e =>
      IO.println s!"[error] {name} — {e}"

#eval checkValidated "7. toValidated index translation" <|
  RawClosedGraph.toValidated {
    darts    := #[10, 11]
    vertices := #[100]
    vertexOf := #[100, 100]
    partner  := #[11, 10]
  }
-- Expected: [ok] 7. toValidated index translation — partnerIdx = #[1, 0], vertexIdx = #[0, 0]
