# Independent audit of the Hanson–Toft family premises

This audit proves full criticality of the entire family, verifies the finite cycle-label lemma without SAT, and checks the induction that reduces the minimal-orientation question to six finite base cases. It does **not** certify those separate base-case UNSAT computations; their exact CNFs and proofs must be checked independently.

## Family and order

Let k ≥ 4 and r = k−3. Take a cycle C₇ with vertices x₀,…,x₆, indexed modulo 7. For each i, add a disjoint clique Qᵢ of order r, joining every vertex of Qᵢ to the three cycle vertices

\[
T_i=\{x_i,x_{i+1},x_{i+3}\}.
\]

The graph Hₖ has

\[
|V(H_k)|=7(k-2),\qquad |E(H_k)|=\frac72(k^2-k-4).
\]

Every host edge has its endpoints in Qᵢ∪Tᵢ for some i. For a cycle edge xᵢxᵢ₊₁, choose block i. For an edge incident with a clique vertex, choose that vertex's clique. Every host vertex also belongs to at least one such block.

## The complete cycle-label lemma

For a proper coloring of C₇, let q be the number of colors used on the cycle and t the number of triples Tᵢ that use exactly two colors. Every triple uses two or three colors because it contains the edge xᵢxᵢ₊₁.

Up to color renaming, all proper cycle colorings are represented by restricted-growth strings of length seven, starting with 0 and introducing any new color with the next unused integer. Exhaustive generation gives the following complete distribution:

| q | t | Number of color partitions |
|---:|---:|---:|
| 3 | 5 | 14 |
| 3 | 6 | 7 |
| 4 | 3 | 35 |
| 4 | 4 | 35 |
| 5 | 2 | 49 |
| 5 | 3 | 7 |
| 6 | 1 | 14 |
| 7 | 0 | 1 |

There are 162 partitions in total. In particular,

\[
q+t\le9,\qquad t\le6.
\]

The standard-library verifier regenerates all 162 partitions, rather than trusting this table.

The proper three-color pattern

\[
(0,1,0,2,1,0,1)
\]

has exactly one three-color triple, T₀. All other six triples use two colors. Rotating the pattern makes Tᵢ the unique three-color triple for any desired i.

## Full criticality for every k ≥ 4

A k-coloring exists: use the displayed three-color pattern on the cycle and the remaining r colors on each Qᵢ.

A coloring with k−1 = r+2 colors cannot exist. The complete cycle-label lemma says that at least one Tᵢ uses three colors. Its adjacent clique Qᵢ would then need r distinct colors drawn from only (r+2)−3 = r−1 colors, a contradiction.

Every edge deletion has a uniform coloring with k−1 colors, in three cases:

1. **Cycle edge.** After deleting xᵢxᵢ₊₁, alternate two colors along the resulting seven-vertex path. Give every Qⱼ the remaining r colors.
2. **Edge inside Qᵢ.** Rotate the cycle pattern so Tᵢ is its unique three-color triple. Every other clique has at least r available colors outside its adjacent triple. For Qᵢ, there are r−1 available colors outside its three ports: give the deleted edge's endpoints the same available color and give its other r−2 vertices distinct remaining available colors. This case exists only when r ≥ 2.
3. **Port edge yxⱼ, with y∈Qᵢ and xⱼ∈Tᵢ.** Use the same rotated cycle pattern. Its three ports have distinct colors. Give y the color of xⱼ, which is permissible precisely because this port edge was deleted; give the other r−1 clique vertices the r−1 colors outside all three ports. Color the other cliques from their available colors.

Each coloring is proper for the stated deletion. Every vertex has an incident edge, so restricting one of these edge-deletion colorings proves that every vertex deletion is also (k−1)-colorable. Thus Hₖ is fully k-critical for every k ≥ 4.

The independent verifier implements these formulas without a coloring solver. It directly checks every individual edge deletion for k=4,…,20: 9,044 deletion colorings in total, as well as the k-colorings. The formulas above establish the unrestricted family; the finite checks are a separate implementation audit.

## The orientation-to-coloring bridge

The lifting argument below concerns proper colorings with exactly one complete increasing path. Its application to arbitrary orientations uses Gallai's established reduction, stated explicitly in Jensen–Toft §13.8, printed page 215: if any orientation has exactly one directed path of length k−1, an acyclic such orientation exists, and its longest-path levels give a proper k-coloring with exactly one complete increasing path. Conversely, such a coloring gives the required orientation by directing each edge toward the larger color. The book source is https://djvu.online/file/sNID8jjCqAw5z. This audit invokes that published equivalence; it does not assume that an arbitrary orientation is acyclic.

## The common-color reduction for k ≥ 10

Consider any proper coloring of Hₖ with the ordered palette 0,…,k−1. There are k−q colors absent from the cycle. A clique whose ports use three colors must use **every** color outside those ports, because its r=k−3 vertices all have different colors. A clique whose ports use two colors omits exactly one of the available k−2 colors.

Thus at most t colors absent from the cycle can fail to occur in at least one clique. Since

\[
k-q>t\quad\text{when }k\ge10
\]

by q+t≤9, some color a is absent from the cycle and occurs in every Qᵢ. Delete its unique vertex from each clique and compress the color order by removing a. The induced remaining graph, with that proper (k−1)-coloring, is exactly Hₖ₋₁.

## Increasing-path insertion is injective

A complete increasing path in the reduced graph uses each of the k−1 remaining colors exactly once. If a is an interior color in the old palette, take the edge between the two colors immediately below and above a. Both endpoints lie in some block Qᵢ∪Tᵢ. The removed a-colored vertex from Qᵢ is adjacent to both endpoints, so insert it between them. The resulting path uses all k colors in increasing order.

If a is the first or last color, take a block containing the corresponding path endpoint and insert that block's removed vertex at the appropriate end. These choices always exist.

The extension sets of distinct reduced paths are disjoint: deleting the unique a-colored vertex from any extended path recovers its reduced path. Consequently the number of complete increasing paths in the original coloring is at least the number in the reduced coloring.

Every proper h-coloring of an h-chromatic graph has at least one complete increasing path. Indeed, orient edges toward larger colors and assign each vertex the maximum length of a directed path ending there. Those lengths form a proper coloring. If there were no path on h vertices, this would use at most h−1 colors, a contradiction.

It follows that an original coloring with exactly one complete increasing path would give a reduced coloring with exactly one such path. Therefore a minimal orientation of Hₖ for k≥10 would imply one of Hₖ₋₁. Repeated reduction reaches H₉. In conjunction with independently certified negative base cases H₄,…,H₉, this proves the all-k negative result. The finite base cases remain a separate proof obligation.

## Reproduce this premise audit

```sh
python independent_family_premises.py
```

Only Python's standard library is used. The result is recorded in `independent_family_premises_receipt.json`. This audit makes no novelty or bibliographic-priority claim.
