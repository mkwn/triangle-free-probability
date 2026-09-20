# An entropy certificate for the triangle variational problem

A Lean formalization of a technical lemma in the paper "Nonlinear lower-tail large deviations at criticality" by Matthew Kwan and Huy Tuan Pham. This lemma is used to solve a certain variational problem, which is necessary to characterise the probability that a random graph is triangle-free in the so-called "critical regime" where the edge probability is of order 1 / sqrt n.
    
Specifically, this lemma defines a "certificate function" G and proves that it satisfies a certain inequality. This involves lots of interval arithmetic. 

The sole advertised lemma is

```lean
TriangleNumerical.entropy_certificate :
  TriangleNumerical.EntropyCertificateProposition
```
This repository has been prepared for use with [Comparator](https://github.com/leanprover/comparator). So, a human who wishes to verify correctness of this lemma only needs to check that [Challenge.lean](Challenge.lean) correctly formalises the lemma statement. (Of course, the reader also needs to trust the Lean kernel and the faithfulness of the definitions in Mathlib).
