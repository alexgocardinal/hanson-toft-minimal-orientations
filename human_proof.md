# Hanson–Toft seven-cycle family: proof and reproducible finite check

**Status (revised after the additional ZIP upload).** The elementary arguments and induction follow from the graph definition. The six exact CNFs and positive-hint LRAT refutations for \(k=4,\ldots,9\) have now been reconstructed and replayed to the empty clause by a standard-library checker. The earlier independent exhaustive enumeration is a second check. Together these give a reproducible **computer-assisted proof** of the family statement. A Lean kernel proof and a definitive historical priority review are still outstanding.

## Definition and statement

For \(k\ge4\), let \(H_k\) have a seven-cycle \(x_0x_1\cdots x_6x_0\), with subscripts modulo seven. For each \(i\), adjoin a disjoint clique \(Q_i\) of order \(k-3\), joined completely to
\[
T_i=\{x_i,x_{i+1},x_{i+3}\}.
\]
There are no other edges. A *full increasing path* in an ordered proper \(k\)-coloring \(c:V(H_k)\to\{0,\dots,k-1\}\) is a path whose successive colors are \(0,1,\dots,k-1\). Write \(P(k)\) for the assertion that every such coloring has at least two distinct full increasing paths.

The theorem is: \(H_k\) is fully \(k\)-critical and \(P(k)\) holds for every \(k\ge4\). By the orientation/coloring equivalence given in Jensen–Toft, *Graph Coloring Problems*, §13.8, pp. 215–216, \(P(k)\) implies that \(H_k\) has no orientation with exactly one directed simple path of length \(k-1\). This equivalence includes arbitrary orientations, not only initially acyclic ones; cite or prove that direction explicitly in a final paper/formalization.

## Elementary seven-cycle lemma

For a proper coloring of \(C_7\), let \(q\) be the number of color classes and \(t\) the number of sets \(T_i\) using exactly two colors. Then
\[
t\le6,\qquad q+t\le9.
\]

**Proof.** Each \(T_i\) contains the cycle edge \(x_ix_{i+1}\). Its two other vertex pairs, \(\{x_i,x_{i+3}\}\) and \(\{x_{i+1},x_{i+3}\}\), have cyclic distances three and two, respectively. As \(i\) varies, these fourteen pairs are exactly the fourteen nonedges of \(C_7\), each occurring once. Since a color class is independent, a two-color \(T_i\) contains exactly one equal-colored nonedge pair, while a three-color \(T_i\) contains none. Thus if the class sizes are \(n_1,\dots,n_q\),
\[
t=\sum_{r=1}^q {n_r\choose2}.
\]
An independent set in \(C_7\) has at most three vertices. If \(a_j\) counts classes of size \(j\), then \(a_1+2a_2+3a_3=7\), \(q=a_1+a_2+a_3\), and \(t=a_2+3a_3\). Consequently \(q+t=7+a_3\le9\). Also, if \(a_3=0,1,2\), respectively, then \(t\le3,5,6\), respectively. ∎

The proper cycle coloring \((0,1,0,2,1,0,1)\) has exactly one three-color attachment triple, \(T_0\). Rotation makes any prescribed \(T_i\) the exceptional triple.

## Full criticality (unconditional)

If a \((k-1)\)-coloring of \(H_k\) existed, each \(Q_i\) would need \(k-3\) colors absent from \(T_i\); hence all \(T_i\) would use at most two colors, giving \(t=7\), a contradiction. A three-coloring of \(C_7\) extends to a \(k\)-coloring: each \(Q_i\) receives \(k-3\) distinct colors outside its triple. Thus \(\chi(H_k)=k\).

Delete any edge \(e\) and use a palette of \(k-1\) colors:

1. If \(e\) is a cycle edge, alternately two-color the resulting seven-vertex path, and fill each \(Q_i\) with distinct colors absent from \(T_i\).
2. If \(e=yx_j\) with \(y\in Q_i\), rotate the displayed exceptional cycle coloring so that \(T_i\) is its unique three-color triple. Color \(y\) as \(x_j\) (the three cycle vertices of \(T_i\) have distinct colors), and assign the other \(k-4\) vertices of \(Q_i\) the \(k-4\) colors outside \(T_i\). Fill every other clique from its at least \(k-3\) available colors.
3. If \(e=uv\) is internal to \(Q_i\) (so \(k\ge5\)), use the same exceptional cycle coloring. Give \(u,v\) one common color outside \(T_i\), and give the other \(k-5\) vertices of \(Q_i\) distinct remaining outside colors. Fill the other cliques as above.

Each graph has no isolated vertices. For every vertex \(v\), restrict a \((k-1)\)-coloring of \(H_k-e\), for an incident edge \(e\), to \(H_k-v\). Thus every edge and vertex deletion lowers the chromatic number; every proper subgraph is contained in such a deletion. This proves full \(k\)-criticality. Also \(|V|=7(k-2)\), \(|E|=7(k^2-k-4)/2\), and \(\Delta=3k-7\).

## Uniform step (unconditional)

**Lemma.** For \(k\ge10\), every proper ordered \(k\)-coloring of \(H_k\) contains a color \(c\) absent from the cycle and present exactly once in each \(Q_i\). Deleting those seven vertices and removing rank \(c\) from the palette produces a proper ordered \((k-1)\)-coloring of a copy of \(H_{k-1}\). There is an injection from its full increasing paths to the full increasing paths of the original coloring.

**Proof.** If \(T_i\) uses three colors, \(Q_i\) must use *every* one of the \(k-3\) colors outside \(T_i\). If \(T_i\) uses two colors, \(Q_i\) uses \(k-3\) of the \(k-2\) colors outside \(T_i\), omitting exactly one. Therefore, among the \(k-q\) colors absent from the cycle, at most \(t\) are omitted by at least one clique. Since \(k>q+t\), a color \(c\) belongs to every \(Q_i\); its vertex there is unique by properness. Deletion shrinks each clique from \(k-3\) to \(k-4\) and leaves all the prescribed adjacencies, hence produces \(H_{k-1}\).

Let \(v_0,\dots,v_{k-2}\) be a full increasing path in the reduced graph, indexed by the compressed colors. If \(c\) is interior, the two vertices with colors immediately below and above \(c\) form an edge. Every edge of the reduced graph lies in at least one \(Q_i\cup T_i\): cycle edges lie in the corresponding \(T_i\), and all remaining edges lie in their own clique and attachment. Insert that block's deleted color-\(c\) vertex between the two endpoints; it is adjacent to both. If \(c\) is the minimum or maximum color, select a block containing the first or last vertex and insert its deleted vertex at the appropriate end. Every vertex belongs to a block. Choose the least suitable index \(i\) to make this rule deterministic. The new vertex was deleted from the reduced graph, so the extended path is simple. Removing its unique color-\(c\) vertex recovers the original reduced path; hence the extension is injective. ∎

For completeness, every proper ordered coloring of a \(j\)-chromatic graph has at least one full increasing path. Orient edges toward larger colors; if all increasing paths had fewer than \(j\) vertices, color every vertex by the maximum number of vertices in an increasing path ending there. This would be a proper coloring using fewer than \(j\) colors, a contradiction.

The same step works whenever a particular coloring has a common absent-cycle color, including \(5\le k\le9\). Thus a finite checker can handle all colorings of \(H_4\), but for \(5\le k\le9\) need handle only *irreducible* colorings, in which no absent-cycle color occurs in every clique. Inductively, any omitted reducible coloring inherits at least two paths from \(H_{k-1}\). For \(k\ge10\), every coloring is reducible by \(q+t\le9\). One must check **all** colorings of \(H_4\): reducing it would yield \(H_3=C_7\), for which the analogous two-path statement fails (for example, the coloring \((0,1,0,1,0,1,2)\) has one \(0,1,2\) path).

The completed finite checks below cover every \(H_4\) coloring and the irreducible \(H_5,\dots,H_9\) colorings. The induction therefore gives \(P(k)\) for all \(k\ge4\).

## Finite verification and its coverage

For \(k=4\), prove \(P(k)\) for all colorings of the exact labeled graph; for \(5\le k\le9\), prove it for all irreducible colorings. One auditable route is a direct finite enumeration, avoiding a SAT proof trace. In every proper cycle coloring, each three-color \(T_i\) forces the colors of \(Q_i\) to be exactly the \(k-3\) outside colors, while each two-color \(T_i\) allows precisely \(k-2\) choices of one omitted outside color. Once the subset of colors in \(Q_i\) is fixed, sorting them on a fixed vertex order loses no case: permutations within that clique are automorphisms.

Here is complete pseudocode, with all arithmetic exact integers and `cap2(z)=min(2,z)`:

```text
for k in 4..9:
  for cycle in {0,...,k-1}^7:
    if some cycle[i] == cycle[(i+1)%7]: continue
    for each i, options[i] = all (k-3)-subsets of
      {0,...,k-1} minus {cycle[i],cycle[(i+1)%7],cycle[(i+3)%7]}
    for (clique_set[0],...,clique_set[6]) in product(options):
      if k >= 5 and ((intersection of all clique_set[i]) minus set(cycle))
         is nonempty: continue  # inherited by induction from H_(k-1)
      color the j-th labeled vertex of each Q_i with
         the j-th smallest element of clique_set[i]
      for v: ways[v] = 1 if color[v] == 0 else 0
      for rank in 1..k-1:
        for v with color[v] == rank:
          ways[v] = cap2(sum(ways[u] for u adjacent to v
                               if color[u] == rank-1))
      assert cap2(sum(ways[v] for v with color[v] == k-1)) == 2
```

The recurrence exactly counts paths up to two, since distinct penultimate vertices give distinct paths, and strict increase makes every path simple. The number of *candidate instances* in this loop can be checked without constructing the graphs. For a cycle coloring with \(q\) used colors and \(t\) two-color triples, there are \((k-2)^t\) sorted-clique choices total. Put \(m=k-q\). By inclusion–exclusion, the irreducible choices number
\[
I(k,q,t)=\sum_{s=0}^{m}(-1)^s {m\choose s}(k-2-s)^t,
\]
because for any specified \(s\) absent-cycle colors to be common to every clique, none can be selected as the omitted color of any two-color triple. The 162 cycle-color partitions, canonically labeled by first occurrence, have the following \((q,t)\) frequencies:
\[
\begin{array}{c|rrrrrrrr}
(q,t)&(3,5)&(3,6)&(4,3)&(4,4)&(5,2)&(5,3)&(6,1)&(7,0)\\\hline
\text{frequency}&14&7&35&35&49&7&14&1
\end{array}
\]
Each partition on \(q\) classes admits \((k)_q=k!/(k-q)!\) distinct rank assignments. These formulas give exact candidate counts, before any path test:

| \(k\) | All sorted-clique colorings | Irreducible colorings | Cases to test |
|---:|---:|---:|---:|
| 4 | 41,664 | 41,160 | **41,664** |
| 5 | 1,039,500 | 832,440 | 832,440 |
| 6 | 10,120,320 | 4,505,760 | 4,505,760 |
| 7 | 59,856,090 | 9,389,520 | 9,389,520 |
| 8 | 258,967,296 | 8,184,960 | 8,184,960 |
| 9 | 902,795,544 | 2,540,160 | 2,540,160 |

The table follows independently from the eight \((q,t)\) frequencies and inclusion–exclusion and checks the loop coverage. The companion `audit_hanson_toft.py` exhausts all 41,664 \(H_4\) colorings and all 1,039,500 sorted-clique \(H_5\) colorings, finding at least two full paths in each case. The companion `irreducible_check.cpp` exhausts 25,452,840 irreducible \(H_5,\dots,H_9\) colorings. Its observed counts equal the table, and every final capped path count is two. A second run with undefined-behavior and bounds instrumentation produced the same counts without diagnostics. Reproduction commands appear in the accompanying README.

## Replayed SAT/LRAT finite certificates

The newly supplied `certificates/` directory contains the exact six base CNFs and LRAT refutations, copied byte-for-byte from `Graph-theory-counterexamples-round-three.zip`, along with an independent standard-library reconstruction and checker. The command

```sh
cd certificates
python verify_family.py
```

regenerates the graph and CNF for every (k=4,ldots,9), compares each clause in order with the archived DIMACS file, checks the graph6 strings, and verifies each positive-hint LRAT addition and the final empty clause. It also enumerates the 162 cycle partitions and checks 9,044 explicit edge-deletion witnesses for (4le kle20); the unrestricted criticality proof above is symbolic.

The formula has exactly-one vertex-color variables (C(v,j)), reachability variables (R(v,j)) saying that at least one path with colors (0,ldots,j) ends at (v), and multiplicity variables (M(v,j)) saying that at least two such paths end at (v). The encoding uses both implications of each auxiliary-gate definition. For (j>0), with (N(v)) the neighbors of (v), its intended recurrences are

\[
R(v,j)\longleftrightarrow C(v,j)\wedge\bigvee_{u\in N(v)}R(u,j-1),
\]
\[
M(v,j)\longleftrightarrow C(v,j)\wedge
\left(\bigvee_{u\in N(v)}M(u,j-1)\ \vee\
\bigvee_{\{u,w\}\subseteq N(v)}(R(u,j-1)\wedge R(w,j-1))\right),
\]
with (R(v,0)\leftrightarrow C(v,0)) and (M(v,0)\leftrightarrow\bot). Paths reaching distinct predecessors differ, and a predecessor with two paths gives two extensions. Increasing color order precludes repeated vertices. At rank (k-1), the formula requires some (R), at most one (R), and no (M); these conditions are equivalent to exactly one full path.

The CNF also sorts the colors assigned within each true-twin clique, rotates a minimum-colored cycle vertex to (x_0), and requires the color at (x_0) to lie in the lower half of the palette. These reductions preserve path counts. For the last one, reverse all color ranks, which bijects a full path with its reversal. If (a,b) are the minimum and maximum ranks appearing on the cycle, then either (a) or (k-1-b) is at most (lfloor(k-1)/2
floor); after the appropriate reversal, rotate a minimum to (x_0) and sort the cliques again. No arbitrary palette permutation is used.

| (k) | CNF variables | CNF clauses | Verified LRAT additions | Empty clause |
|---:|---:|---:|---:|:---:|
| 4 | 622 | 2,274 | 360 | Yes |
| 5 | 1,791 | 7,205 | 1,734 | Yes |
| 6 | 4,066 | 16,972 | 4,003 | Yes |
| 7 | 7,951 | 33,738 | 6,913 | Yes |
| 8 | 14,034 | 60,002 | 11,699 | Yes |
| 9 | 22,987 | 98,599 | 16,194 | Yes |

For each proof addition, `independent/check_lrat.py` assumes the negation of the candidate lemma and checks that its listed **positive** clause hints perform unit propagation to contradiction. It rejects negative/RAT hints. Deletion records may be ignored: every retained clause is already proved a consequence of the original CNF, and retaining more clauses cannot invalidate later RUP additions. The six replays checked 40,903 additions in total. The earlier direct Python/C++ enumeration above gives a separate implementation and finite proof route; it does not rely on this CNF or LRAT checker.

The verification boundary is explicit. Machine replay proves unsatisfiability of the exact finite formulas assuming the correctness of the small Python interpreter, the mathematical explanation of the encoding and symmetry constraints, the elementary reduction, and the published orientation/coloring equivalence. The certificate replay itself is **not** a Lean theorem. The archive manifest and every copied input SHA-256 are retained in `certificates/UPLOADED_FILE_MANIFEST.json`.

## Lean formalization obligations

1. Define labeled \(H_k\) as a finite simple graph and prove the block incidence, edge count/degree formulas if desired, and deletion isomorphism \(H_k\setminus\{q_i(c):i\in\mathbb Z/7\}\cong H_{k-1}\).
2. Formalize the nonedge-pair bijection and the independence bound \(\alpha(C_7)=3\), deriving \(t\le6\) and \(q+t\le9\).
3. Construct the \(k\)-coloring and all edge-deletion \((k-1)\)-colorings; infer full criticality.
4. Define paths as vertex lists with adjacency, distinctness, and successive ranks. Prove the common-color lemma and the deterministic injective insertion map, including both endpoint cases.
5. Establish or import and explicitly state the orientation-to-ordered-coloring equivalence for a unique directed \((k-1)\)-path. The reverse implication needed here must cover cyclic orientations.
6. **Base cases:** translate the completed finite enumeration into Lean reflection and prove its coverage and path-count recurrence, or import the now available CNF/LRAT data through an LRAT checker proved sound in Lean. A Python replay or an imported hash by itself is not a kernel proof. The current Lean file does not establish the theorem.

No claim about present-day novelty follows from these mathematical arguments; priority requires a separate literature check, especially the complete Youngs (1995) paper.
