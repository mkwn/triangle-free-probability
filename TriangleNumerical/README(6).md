# An entropy certificate for the triangle variational problem

A Lean formalization of a technical lemma in the paper "Nonlinear lower-tail large deviations at criticality" by Matthew Kwan and Huy Tuan Pham. This lemma is used to solve a certain variational problem, which is necessary to characterise the probability that a random graph is triangle-free in the so-called "critical regime" where the edge probability is of order 1 / sqrt n.
    
Specifically, this lemma defines a "certificate function" G and proves that it satisfies a certain inequality. This involves lots of interval arithmetic. 

The sole advertised theorem is

```lean
TriangleNumerical.entropy_certificate :
  TriangleNumerical.EntropyCertificateProposition
```

**For a statement-level review, start with [Challenge.lean](Challenge.lean).**
It contains all the definitions needed to interpret the theorem and imports
only Mathlib. The proof is assembled in
[TriangleNumerical/Assembly.lean](TriangleNumerical/Assembly.lean) and exposed
through [Target.lean](Target.lean).

## Pinned environment

The proof uses **Lean 4.28.0** and **Mathlib v4.28.0**, with Mathlib fixed at

```text
8f9d9cff6bd728b17a24e163c9402775d9e6a365
```

Use the supplied toolchain, Lake configuration, and manifest. Initial setup requires [Lean/Elan](https://lean-lang.org/install/), Git, internet access, and sufficient disk space for Mathlib. Run project commands in the repository root, where `lakefile.toml` is located.

## Independent verification with Comparator

[Comparator](https://github.com/leanprover/comparator) compares the submitted
proof with the independently specified challenge, audits its axioms, and
replays the exported proof through a kernel.
