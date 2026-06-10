/-
  EvaluationChecker.lean

  Validates the final evaluation step of a source-reduction certificate.

  After the step checker has proved

      initial  =  final       (in the presentation ideal)

  this checker proves

      Σᵢ  final.terms[i].coefficient × entries[i].evaluation  =  0

  as a polynomial in n.

  ## Trust boundary

  * Python performs canonicalisation and cache lookup.
  * Lean trusts the final LC as already proved by the reduction checker.
  * Lean trusts the evaluation polynomials as supplied in the certificate.
  * Lean's only job here is arithmetic: check the weighted sum equals zero.

  ## Certificate structure

  The `"evaluation_certificate"` field in the main JSON has the form:

    {
      "entries": [
        { "evaluation": { "coefficients": ["6", "0", "0", "-1"] } },
        { "evaluation": { "coefficients": ["3"] } },
        ...
      ]
    }

  One entry per term in the final LC, **in the same positional order**.
  No coefficient or graph is repeated; those already live in the final LC.
-/

import Certificates.Polynomial
import Certificates.JsonDecode

open Polynomial

namespace EvaluationChecker

-- ─── Coefficient parsing ─────────────────────────────────────────────────────

private def parseRat (s : String) : Except String Rat :=
  let t := s.trimAscii.toString
  match t.splitOn "/" with
  | [n] =>
    match n.trimAscii.toString.toInt? with
    | some i => .ok (i : Rat)
    | none   => .error s!"cannot parse '{s}' as integer"
  | [n, d] =>
    match n.trimAscii.toString.toInt?, d.trimAscii.toString.toInt? with
    | some num, some den =>
      if den = 0 then .error s!"zero denominator in '{s}'"
      else .ok ((num : Rat) / (den : Rat))
    | _, _ => .error s!"cannot parse '{s}' as rational"
  | _ => .error s!"malformed rational '{s}'"

private def parseCoeff (c : Coefficient) : Except String Poly := do
  let rats ← c.coefficients.toList.mapM parseRat
  return Polynomial.normalize rats

-- ─── Core checker ────────────────────────────────────────────────────────────

/-- Check the evaluation certificate against the final linear combination.

    Succeeds iff:
    (1) `final.terms.size = cert.entries.size`, and
    (2) the polynomial  Σᵢ final.terms[i].coefficient × entries[i].evaluation
        normalises to zero. -/
def checkEvaluationCertificate
    (final : LinearCombination)
    (cert  : EvaluationCertificate)
    : Except String Unit := do
  -- (1) Length check.
  if final.terms.size ≠ cert.entries.size then
    throw s!"size mismatch: final LC has {final.terms.size} terms but \
             evaluation certificate has {cert.entries.size} entries"
  -- (2) Accumulate Σ coefficient × evaluation.
  let total ← (List.range cert.entries.size).foldlM (fun acc i => do
    let term  ← match final.terms[i]? with
      | some t => pure t
      | none   => throw s!"internal: final.terms[{i}] out of range"
    let entry ← match cert.entries[i]? with
      | some e => pure e
      | none   => throw s!"internal: cert.entries[{i}] out of range"
    let coeff    ← parseCoeff term.coefficient
    let evalPoly ← parseCoeff entry.evaluation
    let contrib  := Polynomial.normalize (Polynomial.mul coeff evalPoly)
    return Polynomial.normalize (Polynomial.add acc contrib))
    ([] : Poly)
  -- (3) Verify the sum is the zero polynomial.
  if !total.isEmpty then
    throw s!"evaluation sum is non-zero: {total}"

end EvaluationChecker
