#!/usr/bin/env python3
"""Copy the narrow Hanson--Toft proof subset from the attached archive.

Run from this directory after extracting the supplied ZIP to ../round3_review.
The copied CNFs and LRAT traces remain byte-for-byte identical to the upload.
"""
from pathlib import Path
from shutil import copy2
import hashlib
import json

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "round3_review" / "round3" / "edge_flows"
DEST = HERE / "certificates"

files = [
    "verify_family.py",
    "independent_family_premises.py",
    "independent_family_premises.md",
    "HansonToft_family_proof.md",
    "independent/reconstruct_capped.py",
    "independent/check_lrat.py",
    "independent/SEMANTIC_AUDIT.txt",
]
for k in range(4, 10):
    files += [
        f"HansonToft_k{k}.json",
        f"HansonToft_k{k}_formula.cnf",
        f"independent/HansonToft_k{k}.lrat.gz",
    ]

entries = []
for name in files:
    src = SOURCE / name
    dst = DEST / name
    dst.parent.mkdir(parents=True, exist_ok=True)
    copy2(src, dst)
    entries.append({"path": name, "sha256": hashlib.sha256(dst.read_bytes()).hexdigest(),
                    "bytes": dst.stat().st_size})
(DEST / "UPLOADED_FILE_MANIFEST.json").write_text(
    json.dumps({"source": "Graph-theory-counterexamples-round-three.zip/round3/edge_flows",
                "copied_files": entries}, indent=2) + "\n"
)
print(f"Copied {len(entries)} byte-identical proof inputs to {DEST}")
