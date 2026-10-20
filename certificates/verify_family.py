#!/usr/bin/env python3
"""One-command standard-library replay of the whole-family certificate.

No solver or third-party package is needed. The mathematical induction is
written in HansonToft_family_proof.md; these checks establish its finite
premises and reconstruct all six certified base formulas exactly.
"""
import argparse,pathlib,subprocess,sys
P=pathlib.Path(__file__).resolve().parent
if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--include-search-records',action='store_true')
    args=parser.parse_args()
    steps=[P/'independent_family_premises.py',P/'independent/reconstruct_capped.py',P/'independent/check_lrat.py']
    if args.include_search_records:steps.append(P/'replay_search_records.py')
    for step in steps:
        print('Checking '+str(step.relative_to(P)),flush=True)
        subprocess.run([sys.executable,str(step)],check=True)
    print('PASS: uniform criticality and cycle lemma; all six exact base formulas and independently checked refutations.',flush=True)
