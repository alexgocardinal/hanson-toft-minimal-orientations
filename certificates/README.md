# Replayed finite certificates for the seven-cycle family

This directory is a narrow, byte-identical subset of the user-supplied
`Graph-theory-counterexamples-round-three.zip` archive. The
`UPLOADED_FILE_MANIFEST.json` records the source archive path,
SHA-256 digest, and size of each of the 25 copied inputs. The JSON receipts
produced by replay are new derived files.

Run `python verify_family.py` here with Python 3. It invokes the
standard-library family premise audit, clause-for-clause reconstruction, and
positive-hint LRAT checker. The six exact formula inputs are
`HansonToft_k4_formula.cnf` through
`HansonToft_k9_formula.cnf`; the six compressed proof inputs
are in `independent/`. Each proof reaches the empty clause.
The run in this workspace is captured in `../certificate_replay.txt`.

The checker ignores deletion records, retaining every earlier checked clause.
This is sound because every added clause is established by a positive-hint
unit-propagation contradiction against the retained consequences. It rejects
negative/RAT hints. The mathematical interpretation of the formula and the
symmetry argument are explained in `../human_proof.md` and in
`independent/SEMANTIC_AUDIT.txt`. The certificate checks are
computer-assisted evidence; no Lean kernel verification is claimed.
