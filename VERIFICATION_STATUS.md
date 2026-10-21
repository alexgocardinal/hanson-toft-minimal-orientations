# Verification status

## Proved in Lean 4.35.0

- The graph has chromatic number k for every k >= 4.
- Every edge deletion and vertex deletion admits a (k-1)-coloring.
- Every proper subgraph admits a (k-1)-coloring.
- The cycle counting bounds t <= 6 and q+t <= 9 hold for arbitrary palettes.
- For k >= 10, a color absent from the cycle occurs in every clique.
- Deleting that color gives the preceding graph and a proper smaller coloring.
- Full increasing paths lift with recovery; distinct paths remain distinct.
- The uniform two-path induction step is proved.
- The family coloring theorem follows conditionally from TwoPathBases.

The six embedded CNFs are proved unsatisfiable using the standard-library
LRAT soundness theorem and `decide +native`. These certificate proofs rely
on native-evaluation axioms; they are not kernel-evaluation-only proofs.
The independent Python certificate replay also passes.

## Still required for the complete theorem

- Formal graph-to-CNF semantics, including the symmetry reductions.
- Full-path existence and the six graph-theoretic two-path base cases.
- The argument covering arbitrary orientations.
- An unconditional proof of completeFamilyStatement.

TwoPathBases is an explicit hypothesis, not a proved theorem or an axiom.
The complete result must not yet be described as fully formalized in Lean.
