# Every Hanson–Toft seven-cycle graph lacks a minimal orientation

Research certificate, 9 October 2026. Mathematical verification and historical priority are separate: the argument below answers the explicitly open family question in Jensen–Toft (1994–95), §13.8, pp.215–216. Targeted source searches have not found an earlier answer, but this is not a complete priority determination. The already refuted general Gallai conjecture is not a new target of this result. The print bibliography gives 1995, its preface is dated 1994, and the official chapter record gives first publication on 3 December 1994; the family question is documented for about 31–32 years, even though the underlying Gallai problem is older.

## Statement and construction

For every integer \(k\ge4\), define \(H_k\) as follows. Begin with the cycle \(x_0x_1\cdots x_6x_0\). For each \(i\in\mathbb Z/7\mathbb Z\), add a disjoint clique \(Q_i\) of order \(k-3\), and join each vertex of \(Q_i\) to every vertex of
\[
T_i=\{x_i,x_{i+1},x_{i+3}\}.
\]
There are no further edges. Then
\[
|V(H_k)|=7(k-2),\qquad |E(H_k)|=\frac{7(k^2-k-4)}2,\qquad \Delta(H_k)=3k-7.
\]

**Theorem.** Every \(H_k\), \(k\ge4\), is fully \(k\)-critical and has no orientation with exactly one directed simple path of length \(k-1\).

Jensen–Toft §13.8 states the equivalence used here: a fully \(k\)-critical graph has a minimal orientation if and only if it has a proper ordered \(k\)-coloring with exactly one simple path whose colors are \(0,1,\ldots,k-1\) in that order. In particular, an arbitrary minimal orientation implies an acyclic one. Consequently, the coloring certificates below cover all orientations, not merely orientations initially assumed acyclic. In the forward construction from a coloring, orient every edge from its smaller color to its larger color; paths of length \(k-1\) must use every color in order.

The theorem uses six finite propositional proofs, for \(k=4,\ldots,9\), and an elementary reduction for every \(k\ge10\). It completes one family question; the six graphs are not six distinct open-problem resolutions.

## A seven-vertex lemma

For a proper coloring of \(C_7\), let \(q\) be the number of colors occurring on the cycle, and let \(t\) be the number of triples \(T_i\) using exactly two colors. Every triple uses two or three colors, since it contains the edge \(x_ix_{i+1}\). Then
\[
t\le6,\qquad q+t\le9.
\]

This finite lemma is independently verified by enumerating every restricted-growth color sequence on seven cyclic positions: start with color 0, and at each next position allow any previously introduced color or exactly the next new color; reject equal adjacent colors, including the closing edge. This enumerates all proper color partitions, independently of palette size. There are exactly 162 partitions. The distribution of \(q+t\) is 99 partitions with value 7, 56 with value 8, and 7 with value 9. The maximum \(t\) is 6. The standard-library script `independent_family_premises.py` enumerates them and checks both inequalities.

The proper cycle coloring
\[
(0,1,0,2,1,0,1)
\]
has exactly one three-color triple, namely \(T_0\). Rotation supplies such a coloring with \(T_i\) as the unique three-color triple for any prescribed \(i\).

## Criticality, uniformly in k

Suppose \(H_k\) had a proper coloring from a palette of \(k-1\) colors. Each \(Q_i\) needs \(k-3\) distinct colors absent from \(T_i\), so every \(T_i\) could use at most two colors. That would give \(t=7\), contradicting the lemma. Thus \(\chi(H_k)\ge k\). A proper three-coloring of the cycle, with each clique colored from any \(k-3\) colors absent on its attachment triple, gives a proper \(k\)-coloring. Hence \(\chi(H_k)=k\).

For every deleted edge, a proper \((k-1)\)-coloring is obtained explicitly:

- If a cycle edge is deleted, the remaining cycle edges form a path on seven vertices. Color this path alternately with two colors. Every attachment triple then uses at most two colors, leaving at least \(k-3\) colors for each clique.
- If an attachment edge \(yx_j\) with \(y\in Q_i\) is deleted, use the rotated cycle coloring with \(T_i\) as the unique three-color triple. Give \(y\) the color of \(x_j\). Give the other \(k-4\) vertices of \(Q_i\) distinct colors outside the three colors of \(T_i\). Each other clique has at least \(k-3\) available colors because its triple uses two colors.
- If an edge \(uv\) inside \(Q_i\) is deleted, again use that rotated cycle coloring. Give \(u,v\) the same color outside the three colors of \(T_i\); give every remaining vertex of \(Q_i\) a distinct other available color. This uses \(k-4\) colors outside the triple. Such an edge exists only when \(k\ge5\), so there is at least one such available color. Color the other cliques as above.

Every graph has no isolated vertices. For any vertex \(v\), choose an incident edge \(e\); a \((k-1)\)-coloring of \(H_k-e\), restricted to \(H_k-v\), proves vertex criticality. Every proper subgraph is contained in an edge or vertex deletion, proving full criticality. The independent premise verifier checks the constructions on every individual edge for \(k=4,\ldots,20\), and the displayed construction applies to every integer \(k\ge4\).

## The finite bases k=4 through 9

The Boolean formula asks whether a proper ordered \(k\)-coloring has exactly one full increasing path. For each vertex \(v\) and rank \(j\), it defines two predicates:

- \(R(v,j)\): at least one path with colors \(0,\ldots,j\) ends at \(v\).
- \(M(v,j)\): at least two distinct such paths end at \(v\).

At rank zero, \(R(v,0)\) is equivalent to “\(v\) has color 0”, and \(M(v,0)\) is false. At positive rank \(j\), \(R(v,j)\) is equivalent to “\(v\) has color \(j\) and some neighbor has \(R(u,j-1)\)”. Similarly, \(M(v,j)\) is equivalent to “\(v\) has color \(j\), and either a neighbor has \(M(u,j-1)\), or two distinct neighbors both have \(R(u,j-1)\)”. Incoming paths from different neighbors are distinct because their penultimate vertices differ. Strict color increase prevents repeated vertices, so this recurrence counts simple paths exactly, capped at two.

The final constraints forbid every \(M(v,k-1)\), and require exactly one \(R(v,k-1)\). All equivalences are expressed in both directions by elementary AND/OR clauses. Exactly-one vertex colors use one positive clause and pairwise exclusions; final at-most-one reachability uses a sequential counter. These formulas are satisfiable exactly when the required coloring exists, subject to the sound normalization below.

Only the following symmetries are used:

1. Vertices within each \(Q_i\) may be permuted to put their colors in strictly increasing numeric vertex order. These vertices have identical neighborhoods outside their clique, so this is a graph automorphism.
2. Rotate the cycle and whole attachment cliques until \(x_0\) has a minimum cycle color.
3. If necessary reverse the entire palette order, and rotate and sort again, to arrange \(\operatorname{color}(x_0)\le\lfloor(k-1)/2\rfloor\). Indeed, either the minimum cycle color already satisfies this, or the reversed minimum is \(k-1-\max\operatorname{color}(C_7)\) and does satisfy it. Reversing both color order and path direction is a bijection of full increasing paths.

These operations preserve the number of full increasing paths. No arbitrary permutation of color ranks is assumed: such a permutation would generally be unsafe for this order-sensitive question.

The files contain the following exact base certificates. The proof-step column counts all recorded proof lines, including deletions; the portable verifier separately reports checked additions.

| k | vertices | edges | maximum degree | variables | clauses | proof lines |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 14 | 28 | 5 | 622 | 2,274 | 673 |
| 5 | 21 | 56 | 8 | 1,791 | 7,205 | 8,097 |
| 6 | 28 | 91 | 11 | 4,066 | 16,972 | 14,573 |
| 7 | 35 | 133 | 14 | 7,951 | 33,738 | 37,940 |
| 8 | 42 | 182 | 17 | 14,034 | 60,002 | 70,245 |
| 9 | 49 | 238 | 20 | 22,987 | 98,599 | 113,693 |

Each formula has a proof of unsatisfiability, checked by `drat-trim`; the checked result is `s VERIFIED` in each stored log. An independent verifier reconstructs every clause, rather than trusting the synthesis code or a claimed formula hash, and checks all six compressed positive-hint LRAT refutations using only the Python standard library. Every hinted propagation clause is checked; all six reach the empty clause. The checks cover 360, 1,734, 4,003, 6,913, 11,699 and 16,194 proof additions, respectively. No SAT solver is needed for replay. The finite statement established is therefore: every proper ordered coloring of every \(H_4,\ldots,H_9\) has a number of full increasing paths different from one. These six bases suffice; the older known cases \(k=4,5\) are also reverified rather than assumed.

## Reduction from k to k−1 for every k≥10

Fix any proper ordered \(k\)-coloring of \(H_k\). Let \(q,t\) describe its cycle coloring. There are \(k-q\) colors absent from the cycle. If a triple uses three colors, its clique uses all \(k-3\) colors absent from that triple. If it uses two, its clique omits exactly one of the \(k-2\) colors absent from the triple. Hence at most \(t\) colors absent from the cycle are omitted by at least one clique.

For \(k\ge10\), the lemma gives \(k>q+t\). Thus some color \(c\), absent from the cycle, occurs in every \(Q_i\). It occurs exactly once in each clique because that clique is properly colored. Delete these seven vertices and remove rank \(c\) from the ordered palette. The result is precisely \(H_{k-1}\), with a proper ordered \((k-1)\)-coloring.

Every full increasing path in this smaller graph extends to a full increasing path in the original graph:

- If \(c\) is an interior rank, take the two consecutive path vertices immediately below and above \(c\). They are adjacent. Every edge of \(H_{k-1}\) belongs to at least one block \(Q_i\cup T_i\). This includes a cycle edge \(x_ix_{i+1}\), which belongs to block \(i\). The deleted color-\(c\) vertex of that clique is adjacent to both ends of the chosen edge. Insert it between them.
- If \(c\) is the smallest or largest rank, choose a block containing the first or last path vertex, respectively, and insert its deleted color-\(c\) vertex at that endpoint. Every vertex belongs to at least one block, and the deleted vertex is adjacent to every remaining vertex of its block.

The inserted vertex was deleted from the smaller graph, so no repetition occurs. Fix, for example, the least block index when there is a choice. This extension is injective: deleting the unique color-\(c\) vertex on an extended path recovers its original smaller path. Therefore the number of full increasing paths in the original coloring is at least the number in the restricted coloring.

Every proper ordered coloring of a graph of chromatic number \(k-1\) has at least one full increasing path, by the Gallai–Hasse–Roy–Vitaver path theorem (or its usual longest-path layering proof for the induced acyclic orientation). If \(H_k\) had exactly one full increasing path, the restricted coloring of \(H_{k-1}\) would consequently have exactly one as well. Repeating the reduction reaches \(H_9\), contrary to the certified base case. Thus none of \(H_k\), \(k\ge10\), has a minimal orientation. Together with the six base cases this proves the theorem.

## Scope, consequences, and files

This proves the entire Hanson–Toft family assertion described as unknown in the 1994–95 book account. It supplies an explicit infinite family of fully critical graphs without minimal orientations, extending the already known first two members. It does not answer the still-open degree-four or triangle-free residual questions: these graphs have triangles and maximum degree \(3k-7\).

Under the book's definition of \(f(k)\) as the largest degree threshold for which every fully \(k\)-critical graph admits a minimal orientation, the family gives \(f(k)\le3k-8\). In particular, the certified \(k=6,7\) graphs give \(f(6)\le10\) and \(f(7)\le13\), versus the upper bounds 14 and 15 stated in the book. These improvements are relative to that published baseline; novelty of the numerical bounds is not yet established by a complete literature review.

All paths below are relative to this directory:

- `pathcount_orientation.py`: discovery encoder and integer-path verification of positive controls.
- `HansonToft_k{k}.json`, for \(k=4,\ldots,9\): exact numeric edge lists, graph6 strings, and formula metadata.
- `HansonToft_k{k}_formula.cnf` and `.cnf.gz`: the six formulas.
- `HansonToft_k{k}_minimal.drup`: the six unsatisfiability proofs.
- `HansonToft_k{k}_minimal_proofcheck.log`: checked `drat-trim` output.
- `HansonToft_base_proof_receipt.json`: proof generation and checker summary.
- `independent_family_premises.py` and its receipt: independent finite cycle lemma and uniform deletion-coloring constructions.
- `independent/reconstruct_capped.py`: independent standard-library formula reconstruction and numeric graph verification.
- `independent/`: independent portable proof verifier and its receipts.

The \(k=10\) time-limited search file is not a proof and is not used. Auxiliary general orientation searches and positive controls elsewhere in the directory are not premises of this theorem.

## Primary sources and status audit

- Tommy R. Jensen and Bjarne Toft, *Graph Coloring Problems*, Wiley, print bibliography 1995 (preface 1994; chapter metadata 3 December 1994), §13.8, pp.215–216. Official chapter record: https://onlinelibrary.wiley.com/doi/10.1002/9781118032497.ch13 . The physical printed-page statement and construction were checked separately; no book scan is redistributed.
- D. A. Youngs, *Minimal orientations of colour critical graphs*, Combinatorica 15 (1995), 289–295, DOI https://doi.org/10.1007/BF01200761 . This is the prior general negative result and the source for the older cases and bounds, not the present whole-family certificate.
- Author updates: https://www.imada.sdu.dk/Research/Graphcol/overview.html .
- Separate dated audit: `../source_audit/JT_13_8_FAMILY_STATUS.md`.

Source retrieval found no indexed later full-family resolution by 9 October 2026. The full published Youngs paper was not recovered: the official PDF request led to a subscription preview. It was accepted on 8 August 1994 and published in June 1995, so added family remarks beyond the book's manuscript account cannot be excluded. That paper must be checked before a novelty claim. The certificate proves the displayed theorem regardless of priority; the current source search does not establish that the question was still open on 9 October 2026.
