# Trivalent Graph Certificates

Lean-checked certificates for obstruction computations in diagrammatic
trivalent graph theories.

This repository accompanies the experimental Sage/Python code in
`cubic-jordan` and `trivalent-graphs`.

The purpose of this repository is *not* to reproduce the large graph
search computations. Instead, it verifies finite exported certificates
produced by those computations.

## Philosophy

The architecture has two layers.

### 1. Certificate generation (Python/Sage)

The Sage code:
- generates closed trivalent graphs,
- constructs source graphs and local substitution sites,
- computes relations,
- performs reductions and evaluations,
- discovers obstruction witnesses,
- exports finite JSON certificates.

These computations are exploratory and computationally intensive.

### 2. Certificate verification (Lean)

Lean reads the exported JSON certificates and verifies:
- graph structure,
- local substitutions,
- occurrence maps,
- replacement correctness,
- reduction traces,
- linear combination arithmetic,
- polynomial identities.

Lean does *not* search for reductions or generate graphs.

The trusted core is therefore reduced to:
- Lean,
- the certificate checker,
- the finite exported certificate data.

## Current target

The initial goal is certification of the F4 obstruction polynomial at
`t = 16`.

The certificate states that certain explicitly listed local relations
evaluate to rational multiples of the obstruction polynomial

\[
n(n-26)(n-14)(n-8)(n-5)(n+1)(n+2)(n-2)^2.
\]

The long-term goal is to extend this to:
- E6 obstruction witnesses,
- reduction traces,
- overlap/critical-pair certificates,
- eventually more general diagrammatic rewriting systems.

## Repository structure

```text
projects/
    exported JSON certificates

Certificates/
    Lean source files

scripts/
    utilities for importing or validating certificates

## Quick verification

Build the checker:

```bash
lake build Certificates.CertCheck
```

Verify a single certificate:

```bash
lake exe cert_check projects/f4/certificates/t10/sources_0000.json
```

The checker should report success and exit with status code 0.

## Friendly verification

The directories

```text
projects/f4/t10
projects/f4/t12
projects/f4/t14

projects/e6/t14
projects/e6/t16
projects/e6/t18
projects/e6/t20
```

contain small and medium-sized certificate collections suitable for quick
verification.

To verify all of these certificates:

```bash
./scripts/check-small.sh
```

This should complete in a reasonable amount of time on ordinary hardware.

## Full verification

The directories

```text
projects/f4/t16
projects/e6/t22
```

contain the largest certificate collections.

To verify every certificate in the repository:

```bash
./scripts/check-all.sh
```

This may take substantially longer.

## Trust boundary

The verification process trusts:

1. Lean.
2. The Lean certificate checker contained in this repository.
3. The exported JSON certificate files.

The Sage/Python code used to generate the certificates is not required for
verification and is not executed during the checking process.
