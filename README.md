# An entropy certificate for the triangle variational problem

A Lean formalization of a technical lemma in the paper ["Nonlinear lower-tail large deviations at criticality"](https://arxiv.org/abs/2610.10233v1) by Matthew Kwan and Huy Tuan Pham. (In version 1 of the arXiv submission it appears as Proposition 7.2). This lemma is used to solve a certain variational problem, which is necessary to characterise the probability that a random graph is triangle-free in the so-called "critical regime" where the edge probability is of order 1 / sqrt n.
    
Specifically, this lemma defines a "certificate function" G and proves that it satisfies a certain inequality. This involves lots of interval arithmetic. The lemma statement appears in this repository as

```lean
TriangleNumerical.entropy_certificate :
  TriangleNumerical.EntropyCertificateProposition
```

This repository has been prepared for use with [Comparator](https://github.com/leanprover/comparator). So, a human who wishes to verify correctness of this lemma only needs to check that [Challenge.lean](Challenge.lean) correctly formalises the lemma statement.


## Building and checking

The project pins Lean **4.35.0-rc2** and the matching Mathlib release. Install
[elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
lake build Challenge TriangleNumerical
lake env lake comparator
```

The first command downloads Mathlib's precompiled dependencies. `lake build`
checks the final proof in `Target`; the next command also checks the independent
Challenge and all auxiliary modules. The Challenge's single `sorry` is
intentional and is never imported by the Solution. `lake env lake comparator`
checks that
`TriangleNumerical.entropy_certificate` in `Target` proves the statement in
`Challenge` using only `propext`, `Classical.choice`, and `Quot.sound`, and
rechecks the proof with the bundled NanoDa kernel. It requires
Bubblewrap (`bwrap`) for its sandbox on Linux. The outer `lake env` puts the
bundled `nanoda_bin` executable on `PATH`.

Every source file uses Lean's module system. Public imports and exposed public
definitions preserve the cross-module reductions used by the interval arithmetic
certificates; their Boolean checks continue to use kernel-checked `decide`.

## Scope and Palomar submission

The compared theorem asserts that for every α ≥ 0 there are an attained global
minimum M of the balanced two-block objective on [0,1]² and a continuous function
G on [0,1] for which `entropyF α G a b c ≥ M` for every a, b, c ∈ [0,1].
The formalization covers this certificate lemma (Proposition 7.2 of the cited
version), rather than the paper's subsequent random-graph probability results.

`comparator.json` selects `Challenge` and `Target`; the latter is the Solution
module, so it does not need to be renamed `Solution.lean`. `formalization.yaml`
records the source, authorship, automation, review status and subject
classifications. The MIT license is in `LICENSE`.
