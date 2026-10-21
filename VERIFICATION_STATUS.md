# Verification status

Lean 4.35.0 proves HansonToft.certified_complete_family_statement : HansonToft.completeFamilyStatement.

For every k >= 4, the development proves chromatic number k, edge and vertex criticality, proper-subgraph colorability, two full increasing paths in every proper ordered k-coloring, and exclusion of exactly one simple directed path on k vertices in any orientation, including cyclic orientations.

The six bases, graph-to-CNF semantics, normalization, family induction, and arbitrary-orientation bridge are proved. TwoPathBases is discharged by certified_two_path_bases.

The reported final dependencies contain no sorryAx. They include propext, Classical.choice, Quot.sound, and native-evaluation axioms for finite checks and LRAT verification. This is not a kernel-evaluation-only proof.

The full build and CI passed for proof commit bbf2a42:
https://github.com/alexgocardinal/hanson-toft-minimal-orientations/actions/runs/39546683223

The manuscript and human-readable proof still need reconciliation with the completed formalization.
