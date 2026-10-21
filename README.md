# Hanson-Toft minimal orientations

Lean 4.35.0 formalization of the seven-cycle family in Jensen and Toft, Graph Coloring Problems, Section 13.8.

The complete theorem is certified_complete_family_statement in CertifiedOrientationFamily.lean. It covers every k >= 4 and arbitrary orientations, including cyclic orientations. The coloring theorem, six finite bases, family induction, and criticality results are proved.

The reported final dependencies contain no sorryAx. Finite checks and certificate verification use native evaluation. See VERIFICATION_STATUS.md for the precise scope and trust boundary.

## Reproduce

    python3 certificates/verify_family.py
    python3 generate_lean_certificates.py --ks 4,5,6,7,8,9
    lake build

The manuscript files are paper_draft.tex and paper_draft.pdf; the human-readable proof is human_proof.md. They are being reconciled with the completed formalization.
