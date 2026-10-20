import argparse
import gzip
import json
from pathlib import Path
from certificates.independent.reconstruct_capped import parse_cnf

TEMPLATE = r'''module
public import Std
public import Std.Tactic.BVDecide.LRAT.Checker
public import Std.Tactic.BVDecide.LRAT.Parser
public meta import Std
public meta import Std.Tactic.BVDecide.LRAT.Checker
public meta import Std.Tactic.BVDecide.LRAT.Parser

public section
namespace HansonToft.CertificateKCASE_NUMBER

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cnfText : String := CNF_LITERAL
def proofText : String := PROOF_LITERAL

def clauseOfText (line : String) : Std.Sat.CNF.Clause Nat :=
  .ofLiterals ((line.splitOn " ").filterMap fun word =>
    match word.toInt? with
    | some i =>
        if i = 0 then none
        else some (i.natAbs - 1, decide (0 < i))
    | none => none)

def formula : Std.Sat.CNF Nat :=
  { clauses := (cnfText.splitOn "\n").toArray.map clauseOfText }

def proofTrace : Array Std.Tactic.BVDecide.LRAT.IntAction :=
  match Std.Tactic.BVDecide.LRAT.parseLRATProof proofText.toUTF8 with
  | .ok trace => trace
  | .error _ => #[]

#eval Std.Tactic.BVDecide.LRAT.check proofTrace formula

theorem formula_unsat : formula.Unsat := by
  apply Std.Tactic.BVDecide.LRAT.check_sound proofTrace formula
  decide +native

#print axioms formula_unsat

end HansonToft.CertificateKCASE_NUMBER
'''

parser = argparse.ArgumentParser()
parser.add_argument("--ks", default="4")
args = parser.parse_args()

for k in map(int, args.ks.split(",")):
    if k not in range(4, 10):
        raise ValueError("Choose cases 4 through 9")
    root = Path("certificates")
    nv, clauses = parse_cnf(root / f"HansonToft_k{k}_formula.cnf")
    ids = {i: i for i in range(1, len(clauses) + 1)}
    records = []
    empty = False

    with gzip.open(root / "independent" / f"HansonToft_k{k}.lrat.gz", "rt") as f:
        for line in f:
            words = line.split()
            if not words or words[0] == "c":
                continue
            if words[1] == "d":
                continue
            original = int(words[0])
            assert original > 0 and original not in ids
            values = list(map(int, words[1:]))
            cut = values.index(0)
            clause, hints = values[:cut], values[cut + 1:]
            assert hints and hints[-1] == 0
            assert all(h > 0 for h in hints[:-1])
            assert all(0 < abs(x) <= nv for x in clause)
            translated = [ids[h] for h in hints[:-1]]
            ident = len(ids) + 1
            records.append(" ".join(map(str, [ident, *clause, 0, *translated, 0])))
            ids[original] = ident
            empty |= not clause

    assert empty
    cnf_text = "\n".join(" ".join(map(str, c)) for c in clauses)
    assert [list(map(int, s.split())) for s in cnf_text.split("\n")] == clauses
    proof_text = "\n".join(records) + "\n"

    source = TEMPLATE.replace("CASE_NUMBER", str(k))
    source = source.replace("CNF_LITERAL", json.dumps(cnf_text))
    source = source.replace("PROOF_LITERAL", json.dumps(proof_text))
    output = Path(f"CertificateK{k}.lean")
    output.write_text(source)
    print(f"Created {output}: {len(clauses)} clauses, {len(records)} additions.")
