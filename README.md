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
certificates/
    exported JSON certificates

Lean/
    Lean source files

scripts/
    utilities for importing or validating certificates

docs/
    notes and examples
