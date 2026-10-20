import argparse
import gzip
from pathlib import Path
from certificates.independent.reconstruct_capped import parse_cnf

def arr(xs):
    return "#[" + ", ".join(map(str, xs)) + "]"

parser = argparse.ArgumentParser()
parser.add_argument("--ks", default="4")
args = parser.parse_args()

for k in map(int, args.ks.split(",")):
    if k not in range(4, 10):
        raise ValueError("Choose cases 4 through 9")
    root = Path("certificates")
    nv, clauses = parse_cnf(root / f"HansonToft_k{k}_formula.cnf")
    renumber = {i: i for i in range(1, len(clauses) + 1)}
    lines = [
        "module",
        "public import Std.Sat.CNF.Basic",
        "public import Std.Tactic.BVDecide.LRAT.Actions",
        "public import Std.Tactic.BVDecide.LRAT.Checker",
        "import all Std.Tactic.BVDecide.LRAT.Checker",
        "import all Std.Sat.CNF.Basic",
        "import all Std.Sat.CNF.Literal",
        "import all Std.Tactic.BVDecide.LRAT.Internal.Basic",
        "import all Std.Tactic.BVDecide.LRAT.Internal.Assignment",
        "import all Std.Tactic.BVDecide.LRAT.Internal.Add",
        "import all Std.Tactic.BVDecide.LRAT.Internal.Delete",
        "import all Std.Tactic.BVDecide.LRAT.Internal.Rup",
        "import all Std.Tactic.BVDecide.LRAT.Internal.Empty",
        "import all Std.Tactic.BVDecide.LRAT.Internal.Rat",
        "import all Std.Tactic.BVDecide.LRAT.Internal.Checker",
        "public section",
        f"namespace HansonToft.CertificateK{k}",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 2000000",
        "def formula : Std.Sat.CNF Nat := { clauses := #["
    ]
    for clause in clauses:
        literals = ", ".join(
            f"({abs(x)-1}, {str(x > 0).lower()})" for x in clause
        )
        lines.append(f"Std.Sat.CNF.Clause.ofLiterals [{literals}],")
    lines += [
        "] }",
        "def proofTrace : Array Std.Tactic.BVDecide.LRAT.IntAction := #["
    ]
    with gzip.open(root / "independent" / f"HansonToft_k{k}.lrat.gz", "rt") as f:
        for line in f:
            words = line.split()
            if not words or words[0] == "c":
                continue
            if words[1] == "d":
                continue
            old_ident = int(words[0])
            assert old_ident not in renumber
            ident = len(renumber) + 1
            values = list(map(int, words[1:]))
            cut = values.index(0)
            clause, hints = values[:cut], values[cut+1:]
            assert hints[-1] == 0
            hints = hints[:-1]
            assert all(h > 0 for h in hints)
            assert all(0 < abs(x) <= nv for x in clause)
            hints = [renumber[h] for h in hints]
            renumber[old_ident] = ident
            if clause:
                lines.append(f".addRup {ident} {arr(clause)} {arr(hints)},")
            else:
                lines.append(f".addEmpty {ident} {arr(hints)},")
    lines += [
        "]",
        "#eval Std.Tactic.BVDecide.LRAT.check proofTrace formula",
        "theorem formula_unsat : formula.Unsat := by",
        "  apply Std.Tactic.BVDecide.LRAT.check_sound proofTrace formula",
        "  decide +native",
        "#print axioms formula_unsat",
        f"end HansonToft.CertificateK{k}"
    ]
    for first_line, last_line, prefix, element_type in [
        (
            "def formula : Std.Sat.CNF Nat := { clauses := #[",
            "] }",
            "formulaChunk",
            "Std.Sat.CNF.Clause Nat"
        ),
        (
            "def proofTrace : Array Std.Tactic.BVDecide.LRAT.IntAction := #[",
            "]",
            "proofChunk",
            "Std.Tactic.BVDecide.LRAT.IntAction"
        ),
    ]:
        first = lines.index(first_line)
        last = lines.index(last_line, first + 1)
        records = lines[first + 1:last]
        replacement = []
        names = []
        for j in range(0, len(records), 64):
            name = f"{prefix}{j // 64}"
            names.append(name)
            replacement.append(f"def {name} : Array ({element_type}) := #[")
            replacement.extend(records[j:j + 64])
            replacement.append("]")
        joined = "(#[" + ", ".join(names) + "]).foldl (fun xs ys => xs ++ ys) #[]"
        if prefix == "formulaChunk":
            replacement.append(
                "def formula : Std.Sat.CNF Nat := { clauses := " + joined + " }"
            )
        else:
            replacement.append(
                "def proofTrace : Array Std.Tactic.BVDecide.LRAT.IntAction := " + joined
            )
        lines[first:last + 1] = replacement

    output = Path(f"CertificateK{k}.lean")
    output.write_text("\n".join(lines) + "\n")
    print(f"Created {output}; Lean must still check it.")
