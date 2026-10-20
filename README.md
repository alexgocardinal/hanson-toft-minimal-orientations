# Hanson–Toft minimal orientations

Research files for the Hanson–Toft seven-cycle family discussed in
Jensen and Toft, Graph Coloring Problems, Section 13.8.

## Verification status

The package contains a computer-assisted mathematical argument and six
CNF/LRAT certificates for k = 4,...,9.

Lean 4.35.0 successfully checks unsatisfiability of all six embedded CNFs
using its standard-library LRAT soundness theorem and `decide +native`.
These proofs rely on native evaluation.

The complete graph-theoretic result is NOT yet fully formalized in Lean.
In particular, the graph-to-CNF connection and the infinite-family
arguments remain formalization obligations.

See VERIFICATION_STATUS.md for the precise scope.

## Reproduce the checks

From the project directory:

    python3 certificates/verify_family.py
    python3 generate_lean_certificates.py --ks 4,5,6,7,8,9
    lake build

The lean-toolchain file pins the compiler version.

## Main files

- paper_draft.tex and paper_draft.pdf: manuscript.
- human_proof.md: mathematical argument and computational details.
- HansonToft.lean: graph definitions and target statements.
- GraphLemmas.lean and CycleCheck.lean: elementary proved facts.
- CertificateK4.lean through CertificateK9.lean: finite CNF proofs.
- certificates/: original formulas, compressed proof traces, and replay code.
- generate_lean_certificates.py: conversion to Lean certificate modules.

A successful build establishes the implemented lemmas and certificate
theorems, not the complete family statement.
