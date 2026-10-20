#!/usr/bin/env python3
"""Independent standard-library reconstruction of archived capped-path CNFs.
No imports from the search program, NetworkX or PySAT.
"""
import itertools,json,gzip,hashlib
from pathlib import Path
P=Path(__file__).resolve().parent;SOURCE=P.parent

def expected_family(k):
 n=7*(k-2); edges={tuple(sorted((i,(i+1)%7)))for i in range(7)}
 cliques=[]
 for i in range(7):
  Q=list(range(7+i*(k-3),7+(i+1)*(k-3)));cliques.append(Q)
  edges.update(itertools.combinations(Q,2))
  edges.update(tuple(sorted((v,(i+j)%7)))for v in Q for j in(0,1,3))
 return n,sorted(edges),cliques

def reconstruct(k):
 n,E,Qs=expected_family(k); adj=[set()for _ in range(n)]
 for u,v in E:adj[u].add(v);adj[v].add(u)
 clauses=[];nv=0
 def variable():
  nonlocal nv;nv+=1;return nv
 C=[[variable()for _ in range(k)]for _ in range(n)]
 R=[[variable()for _ in range(k)]for _ in range(n)]
 M=[[variable()for _ in range(k)]for _ in range(n)]
 def disjunction(xs):
  z=variable()
  clauses.extend([[-x,z]for x in xs]);clauses.append([-z]+xs)
  return z
 def conjunction(xs):
  z=variable()
  clauses.extend([[-z,x]for x in xs]);clauses.append([z]+[-x for x in xs])
  return z
 for v in range(n):
  clauses.append(C[v][:])
  clauses.extend([[-C[v][a],-C[v][b]]for a,b in itertools.combinations(range(k),2)])
 for u,v in E:clauses.extend([[-C[u][a],-C[v][a]]for a in range(k)])
 for Q in Qs:
  for u,v in zip(Q,Q[1:]):
   clauses.extend([[-C[u][a],-C[v][b]]for a in range(k)for b in range(a+1)])
 for v in range(1,7):
  clauses.extend([[-C[0][a],-C[v][b]]for a in range(k)for b in range(a)])
 for v in range(n):
  clauses.extend([[-R[v][0],C[v][0]],[-C[v][0],R[v][0]],[-M[v][0]]])
  for a in range(1,k):
   reach=disjunction([R[u][a-1]for u in sorted(adj[v])])
   r=conjunction([C[v][a],reach]);clauses.extend([[-R[v][a],r],[-r,R[v][a]]])
   alternatives=[M[u][a-1]for u in sorted(adj[v])]
   alternatives.extend(conjunction([R[u][a-1],R[w][a-1]])for u,w in itertools.combinations(sorted(adj[v]),2))
   multi=disjunction(alternatives);m=conjunction([C[v][a],multi])
   clauses.extend([[-M[v][a],m],[-m,M[v][a]]])
 last=[R[v][k-1]for v in range(n)]
 clauses.append(last[:]);clauses.extend([[-M[v][k-1]]for v in range(n)])
 # Independent Sinz sequential at-most-one, using exactly n-1 auxiliaries.
 aux=[variable()for _ in range(n-1)]
 clauses.append([-last[0],aux[0]])
 for j in range(1,n-1):
  clauses.extend([[-aux[j-1],aux[j]],[-last[j],-aux[j-1]],[-last[j],aux[j]]])
 clauses.append([-last[-1],-aux[-1]])
 clauses.append([C[0][a]for a in range((k+1)//2)])
 return n,E,nv,clauses

def parse_cnf(path):
 raw=gzip.open(path,'rt')if path.suffix=='.gz'else path.open()
 clauses=[];nv=None;nc=None
 with raw as f:
  for line in f:
   if not line.strip()or line.startswith('c'):continue
   if line.startswith('p'):
    p=line.split();nv=int(p[2]);nc=int(p[3]);continue
   xs=list(map(int,line.split()));assert xs[-1]==0;clauses.append(xs[:-1])
 assert nc==len(clauses)
 return nv,clauses

if __name__=='__main__':
 rows=[]
 for k in range(4,10):
  rec=json.loads((SOURCE/f'HansonToft_k{k}.json').read_text())
  n,E,nv,clauses=reconstruct(k)
  assert n==rec['n']and E==[tuple(e)for e in rec['edges']]
  es=set(E);bits=[int((u,v)in es)for v in range(1,n)for u in range(v)];bits+=[0]*(-len(bits)%6)
  graph6=chr(n+63)+''.join(chr(63+sum(bits[j+t]<<(5-t)for t in range(6)))for j in range(0,len(bits),6))
  assert graph6==rec['graph6']
  for ext in('.cnf','.cnf.gz'):
   f=SOURCE/f'HansonToft_k{k}_formula{ext}'
   if f.exists():
    actual_nv,actual=parse_cnf(f);assert actual_nv==nv and actual==clauses,(k,ext)
  rows.append({'k':k,'n':n,'m':len(E),'variables':nv,'clauses':len(clauses),'exact_ordered_cnf_reconstruction':'VERIFIED','numeric_order_graph6':'VERIFIED','cnf_sha256':hashlib.sha256((SOURCE/f'HansonToft_k{k}_formula.cnf').read_bytes()).hexdigest()})
 print(json.dumps(rows,indent=2));(P/'reconstruction_results.json').write_text(json.dumps(rows,indent=2)+'\n')
