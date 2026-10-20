# Lean development

Compiler: Lean 4.35.0, pinned in lean-toolchain.

Build the implemented proofs with:

    lake build

Regenerate the six certificate modules with:

    python3 generate_lean_certificates.py --ks 4,5,6,7,8,9

The generator assigns consecutive clause IDs, rewrites hint references,
omits deletions, and embeds numeric data as text parsed inside Lean.

The certificate proofs use the standard-library LRAT soundness theorem
and `decide +native`. Their axiom reports include native-evaluation
axioms. They are not kernel-evaluation-only proofs.

The certificate conclusions concern the embedded CNFs. The connection
to proper graph colorings, symmetry completeness, criticality, the
uniform reduction, and the arbitrary-orientation argument remain to be
proved in Lean.

See VERIFICATION_STATUS.md for the complete verification boundary.

Additional proved structural lemmas are in BlockLemmas.lean,
PathInsertion.lean, SimplePathExtension.lean, and PathRecovery.lean.
They establish block incidence, available insertion vertices, structural
path insertion, and list recovery. They do not yet establish the full
ordered-color path extension or the infinite reduction.
