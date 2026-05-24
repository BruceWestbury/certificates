
# DESIGN.md

## Purpose

This repository contains Lean-checkable certificates for computations in
diagrammatic trivalent graph theories.

The repository is intentionally much smaller in scope than the
experimental Sage codebase.

The Sage code discovers computations.
This repository verifies them.

---

# Architectural overview

There are two layers.

## Layer 1: Certificate generation (external)

External Sage/Python code computes:
- graph generation,
- source construction,
- local substitutions,
- reductions,
- evaluations,
- obstruction witnesses.

The result is exported as finite JSON certificates.

This repository assumes those certificates already exist.

No graph search or reduction search should occur inside Lean.

---

## Layer 2: Certificate verification (Lean)

Lean checks:
- graph well-formedness,
- occurrence validity,
- correctness of local substitutions,
- correctness of reduction traces,
- linear combination arithmetic,
- polynomial factorisations and identities.

The Lean side should remain deterministic and explicit.

---

# Initial scope

The initial scope is intentionally narrow.

We certify only:
- closed connected trivalent graphs,
- F4 source graphs with one distinguished 4-valent vertex,
- local substitution correctness,
- obstruction witness computations.

We do NOT initially formalise:
- arbitrary diagrammatic categories,
- tensor products,
- boundary objects,
- full rewriting systems,
- confluence theory,
- graph generation algorithms.

---

# Core certificate object

The basic certificate unit is a local substitution step.

Conceptually:

```text
host graph
+ occurrence of lhs
+ rhs replacement
=
result graph

# Core mathematical objects

The Lean checker is intentionally based on a very small collection of
explicit combinatorial objects.

The goal is not to formalise a general diagrammatic category or a full
rewriting system. The goal is to certify finite exported obstruction
certificates.

The central principle is:

> Lean checks finite local compatibility statements.
> Lean does not perform search or rewriting.

---

# Closed graphs

A *closed graph* is a finite connected dart graph in which every vertex
has valence 3.

A dart graph consists of:
- a finite set of darts;
- a fixed-point-free involution pairing darts into edges;
- a finite set of vertices;
- an incidence map assigning each dart to its incident vertex.

For closed graphs:
- every dart is paired;
- every vertex is incident to exactly three darts.

---

# Graphs with boundary

A *graph with boundary* is a dart graph together with an ordered list of
boundary darts.

Boundary darts are unpaired darts.

The ordering is part of the structure.

Graphs with boundary arise as complements of local occurrences inside
closed graphs.

---

# Occurrences

An occurrence of a graph with boundary `L` inside a closed graph `G`
consists of:
- an injective map on darts;
- an injective map on vertices;

preserving:
- incidence;
- edge pairings;
- boundary structure.

The occurrence identifies a local region of `G` isomorphic to `L`.

---

# Complements

Given an occurrence `L → G`, the complement `G / L` is obtained by:
- removing the interior darts and vertices of the image of `L`;
- retaining the exposed boundary darts.

The result is a graph with boundary.

The Lean checker does not implement gluing operations.

Instead, substitutions are verified by comparing complements.

---

# Certified substitutions

A substitution certificate contains:

- a closed graph `G`;
- a closed graph `H`;
- a graph with boundary `L`;
- a graph with boundary `R`;
- an occurrence `L → G`;
- an occurrence `R → H`.

Lean computes:
- the complement `G / L`;
- the complement `H / R`.

The substitution is certified if:
- both complements are well-defined;
- the complements are isomorphic as graphs with boundary.

Conceptually:

```text
G / L  ≅  H / R
