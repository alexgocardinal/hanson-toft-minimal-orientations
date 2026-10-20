# Verification status

## Successfully checked in Lean 4.35.0

- The graph definitions compile.
- Adjacency is symmetric and irreflexive.
- The finite cycle-checking program returns true.
- Each embedded CNF for k = 4, 5, 6, 7, 8, 9 is unsatisfiable,
  using Lean's standard-library LRAT soundness theorem and native evaluation.
- The implemented project modules build successfully.
- Block incidence and available insertion vertices are proved.
- Structural interior path insertion preserves adjacency and distinctness.
- List recovery by deletion and the resulting distinctness principle are proved.

The certificate theorems use `decide +native`. Their axiom reports include
the native-evaluation axiom, so they rely on Lean's native computation
infrastructure. They are not kernel-evaluation-only certificate proofs.

## Not yet formally proved

- That every hypothetical unique-path graph coloring yields a satisfying
  assignment of the corresponding embedded CNF, including symmetry reductions.
- That the finite cycle program covers all proper cycle colorings.
- Chromatic number and criticality for the entire graph family.
- The common-color reduction and injective path extension for all k.
- The passage from arbitrary orientations to ordered colorings.
- The complete family theorem stated in HansonToft.lean.

The Python certificate replay also passes independently. The human-readable
argument remains a computer-assisted proof; the complete graph-theoretic
result must not yet be described as fully formalized in Lean.
