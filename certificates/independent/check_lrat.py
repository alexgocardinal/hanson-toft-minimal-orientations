#!/usr/bin/env python3
"""Standard-library checker for these positive-hint LRAT/RUP refutations.
Each hint must identify an existing unit or conflicting clause under the
negated proposed lemma. Negative (RAT) hints are rejected. Deletions may be
ignored because every retained lemma is independently checked to follow from
the exact reconstructed initial formula. No SAT solver is required.
"""
import argparse,gzip,json,time,hashlib
from pathlib import Path
from reconstruct_capped import parse_cnf,reconstruct
P=Path(__file__).resolve().parent

def verify(k):
 formula=P.parent/f'HansonToft_k{k}_formula.cnf'
 proof=P/f'HansonToft_k{k}.lrat.gz'
 if not proof.exists():proof=P/f'HansonToft_k{k}.lrat'
 nv,initial=parse_cnf(formula);n,E,en,expected=reconstruct(k)
 assert nv==en and initial==expected
 clauses={i+1:tuple(c)for i,c in enumerate(initial)}
 added=0;deletions=0;hints_total=0;empty=False;t0=time.monotonic()
 opener=gzip.open if proof.suffix=='.gz'else open
 with opener(proof,'rt')as f:
  for line_no,line in enumerate(f,1):
   tok=line.split()
   if not tok or tok[0]=='c':continue
   if len(tok)>1 and tok[1]=='d':deletions+=1;continue
   idx=int(tok[0]);assert idx not in clauses,('REUSED_ID',k,line_no,idx)
   rest=list(map(int,tok[1:]));cut=rest.index(0)
   lemma=tuple(rest[:cut]);hints=rest[cut+1:];assert hints[-1]==0;hints=hints[:-1]
   assert all(0<abs(l)<=nv for l in lemma)
   assert all(i>0 and i in clauses for i in hints),('NON_RUP_HINT',k,line_no)
   ass={};conflict=False
   for lit in lemma:
    v=abs(lit);value=lit<0
    if v in ass and ass[v]!=value:conflict=True;break
    ass[v]=value
   for h in hints:
    hints_total+=1
    if conflict:break
    remaining=[];satisfied=False
    for lit in clauses[h]:
     v=abs(lit)
     if v not in ass:remaining.append(lit)
     elif ass[v]==(lit>0):satisfied=True;break
    assert not satisfied,('SATISFIED_HINT',k,line_no,h)
    remaining=list(dict.fromkeys(remaining))
    assert len(remaining)<=1,('NONUNIT_HINT',k,line_no,h,remaining)
    if not remaining:conflict=True;break
    lit=remaining[0];ass[abs(lit)]=lit>0
   assert conflict,('NO_CONTRADICTION',k,line_no,lemma)
   clauses[idx]=lemma;added+=1;empty|=not lemma
 assert empty,('NO_EMPTY_CLAUSE',k)
 return {'k':k,'n':n,'m':len(E),'exact_cnf':'VERIFIED','proof_result':'VERIFIED_POSITIVE_HINT_LRAT','checked_lemmas':added,'ignored_deletion_records':deletions,'checked_hint_clauses':hints_total,'empty_clause':'VERIFIED','seconds':time.monotonic()-t0,'cnf_sha256':hashlib.sha256(formula.read_bytes()).hexdigest(),'lrat_sha256':hashlib.sha256(proof.read_bytes()).hexdigest()}

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--ks',default='4,5,6,7,8,9');a=p.parse_args();rows=[]
 for k in map(int,a.ks.split(',')):
  r=verify(k);rows.append(r);print(json.dumps(r),flush=True)
  out=P/'lrat_results.json';tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(rows,indent=2)+'\n');tmp.replace(out)
