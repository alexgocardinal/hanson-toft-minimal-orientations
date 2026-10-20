#!/usr/bin/env python3
"""Independent, standard-library-only Hanson--Toft family premise verifier.

Checks all proper C7 color partitions, the q+t<=9 lifting lemma, and
constructs proper deletion colorings uniformly for every individual edge.
The construction is symbolic in k; finite checks here cover k=4,...,20.
It does not verify the separate finite orientation UNSAT proofs.
"""
import itertools,collections,json,pathlib
P=pathlib.Path(__file__).parent
T=[(i,(i+1)%7,(i+3)%7) for i in range(7)]
def partitions():
    def rec(seq):
        if len(seq)==7:
            if all(seq[i]!=seq[(i+1)%7] for i in range(7)):yield tuple(seq)
            return
        for c in range(max(seq)+2):
            if seq[-1]!=c:yield from rec(seq+[c])
    yield from rec([0])
patterns=list(partitions());assert len(patterns)==162
table=collections.Counter()
for c in patterns:
    q=len(set(c));t=sum(len({c[v] for v in triple})==2 for triple in T)
    assert all(len({c[v] for v in triple}) in (2,3) for triple in T)
    assert q+t<=9 and t<=6
    table[q,t]+=1
assert max(q+t for q,t in table)==9 and max(t for q,t in table)==6
one_bad=(0,1,0,2,1,0,1)
assert all(one_bad[i]!=one_bad[(i+1)%7] for i in range(7))
assert [i for i,triple in enumerate(T) if len({one_bad[v] for v in triple})==3]==[0]
def graph(k):
    assert k>=4;r=k-3
    blocks=[list(range(7+i*r,7+(i+1)*r)) for i in range(7)]
    edges={tuple(sorted((i,(i+1)%7))) for i in range(7)}
    for i,B in enumerate(blocks):
        edges.update(itertools.combinations(B,2))
        edges.update(tuple(sorted((a,b))) for a in T[i] for b in B)
    n=7+7*r
    assert len(edges)==7*(k*k-k-4)//2
    return n,blocks,edges
def check(c,k,edges):
    assert all(a in range(k) for a in c)
    assert all(c[u]!=c[v] for u,v in edges)
def full_coloring(k):
    n,B,E=graph(k);c=[0]*n;c[:7]=one_bad
    for Q in B:
        for j,v in enumerate(Q):c[v]=j+3
    check(c,k,E);return c
def deletion_coloring(k,e):
    n,B,E=graph(k);assert e in E;r=k-3;c=[0]*n
    if e[1]<7:
        i=next(i for i in range(7) if tuple(sorted((i,(i+1)%7)))==e)
        for s in range(7):c[(i+1+s)%7]=s%2
        for Q in B:
            for j,v in enumerate(Q):c[v]=j+2
    else:
        i=next(i for i,Q in enumerate(B) if e[1] in Q)
        for j in range(7):c[(i+j)%7]=one_bad[j]
        for h,Q in enumerate(B):
            available=[a for a in range(k-1) if a not in {c[v] for v in T[h]}]
            if h!=i:
                assert len(available)>=r
                for v,a in zip(Q,available):c[v]=a
            elif e[0]<7:
                port,clique=e;assert port in T[h]
                c[clique]=c[port]
                assert len(available)==r-1
                for v,a in zip([v for v in Q if v!=clique],available):c[v]=a
            else:
                assert r>=2 and e[0] in Q and len(available)==r-1
                c[e[0]]=c[e[1]]=available[0]
                for v,a in zip([v for v in Q if v not in e],available[1:]):c[v]=a
    check(c,k-1,E-{e});return c
results=[]
for k in range(4,21):
    n,B,E=graph(k);full_coloring(k)
    for e in sorted(E):deletion_coloring(k,e)
    assert all(any(v in e for e in E) for v in range(n))
    # Every host edge has a block whose deleted-color vertex is adjacent
    # to both ends, as needed for the increasing-path insertion argument.
    for e in E:
        assert any(set(e)<=set(Q)|set(T[i]) for i,Q in enumerate(B))
    results.append({'k':k,'n':n,'m':len(E),'all_edge_deletion_colorings_checked':len(E)})
receipt={'cycle_partition_count':len(patterns),'maximum_q_plus_t':9,
         'maximum_two_color_triples':6,'one_three_color_triple_pattern':one_bad,
         'q_t_distribution':[{'q':q,'t':t,'count':v} for (q,t),v in sorted(table.items())],
         'family_checks':results,
         'scope':'Criticality and induction premises only; finite orientation UNSAT base cases checked separately.'}
(P/'independent_family_premises_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: all162 proper C7 color partitions; q+t<=9 and t<=6; unique-three-color-triple pattern.')
print('PASS: symbolic uniform k-coloring and every edge-deletion (k-1)-coloring for k=4..20:',sum(r['m'] for r in results),'individual deletion witnesses.')
print('PASS: no isolated vertices, hence full vertex criticality; every edge lies in an insertion block.')
