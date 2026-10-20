#!/usr/bin/env python3
"""Independent finite checks of the Hanson--Toft C7 construction.

Vertices 0..6 represent x_i.  Vertex 7+i*(k-3)+a represents the a-th
vertex of Q_i.  This script uses no routines or certificates named by the PDF.
"""

from __future__ import annotations

from collections import Counter
from itertools import combinations, product
import argparse
from math import comb, prod


def graph(k: int) -> list[set[int]]:
    assert k >= 4
    n = 7 * (k - 2)
    adj = [set() for _ in range(n)]

    def edge(u: int, v: int) -> None:
        adj[u].add(v)
        adj[v].add(u)

    for i in range(7):
        edge(i, (i + 1) % 7)
        clique = [7 + i * (k - 3) + a for a in range(k - 3)]
        for a, u in enumerate(clique):
            for v in clique[a + 1 :]:
                edge(u, v)
            for j in (i, (i + 1) % 7, (i + 3) % 7):
                edge(u, j)
    return adj


def graph6(adj: list[set[int]]) -> str:
    """Standard graph6 serialization (the small and medium n formats)."""
    n = len(adj)
    if n <= 62:
        prefix = chr(n + 63)
    elif n <= 258047:
        prefix = "~" + "".join(chr(63 + ((n >> shift) & 63))
                               for shift in (12, 6, 0))
    else:
        raise ValueError("n is too large for this graph6 function")
    bits = [int(i in adj[j]) for j in range(1, n) for i in range(j)]
    bits.extend([0] * (-len(bits) % 6))
    return prefix + "".join(chr(63 + sum(bits[p + t] << (5 - t)
                                     for t in range(6)))
                            for p in range(0, len(bits), 6))


def cycle_partitions() -> list[tuple[int, ...]]:
    out = []

    def extend(seq: tuple[int, ...]) -> None:
        if len(seq) == 7:
            if seq[-1] != seq[0]:
                out.append(seq)
            return
        for color in range(max(seq) + 2):
            if color != seq[-1]:
                extend(seq + (color,))

    extend((0,))
    return out


def cycle_stats(seq: tuple[int, ...]) -> tuple[int, int]:
    q = len(set(seq))
    t = sum(len({seq[i], seq[(i + 1) % 7], seq[(i + 3) % 7]}) == 2
            for i in range(7))
    return q, t


def irreducible_count(k: int, partitions: list[tuple[int, ...]]) -> int:
    """Inclusion-exclusion total for sorted-clique irreducible colorings."""
    multiplicities = Counter(map(cycle_stats, partitions))
    total = 0
    for (q, t), count in multiplicities.items():
        if q > k:
            continue
        h = k - q
        surjective_cover = sum((-1) ** j * comb(h, j) * (k - 2 - j) ** t
                               for j in range(h + 1))
        total += count * prod(range(k - q + 1, k + 1)) * surjective_cover
    return total


def capped_path_count(adj: list[set[int]], colors: tuple[int, ...], k: int) -> int:
    """Count full increasing paths with saturation at two."""
    prev = [int(c == 0) for c in colors]
    for j in range(1, k):
        prev = [min(2, sum(prev[u] for u in adj[v])) if colors[v] == j else 0
                for v in range(len(adj))]
    return min(2, sum(prev))


def exact_path_count(adj: list[set[int]], colors: tuple[int, ...], k: int) -> int:
    prev = [int(c == 0) for c in colors]
    for j in range(1, k):
        prev = [sum(prev[u] for u in adj[v]) if colors[v] == j else 0
                for v in range(len(adj))]
    return sum(prev)


def all_edges(adj: list[set[int]]) -> list[tuple[int, int]]:
    return [(u, v) for u in range(len(adj)) for v in sorted(adj[u]) if u < v]


def edge_deletion_coloring(k: int, deleted: tuple[int, int]) -> tuple[int, ...]:
    """Explicit proper (k-1)-coloring after each possible edge deletion."""
    u, v = deleted
    if u > v:
        u, v = v, u
    special = (0, 1, 0, 2, 1, 0, 1)
    palette = range(k - 1)

    if v < 7:
        assert v == (u + 1) % 7 or (u, v) == (0, 6)
        start = (u + 1) % 7 if v == (u + 1) % 7 else 0
        cycle = [0] * 7
        for offset in range(7):
            cycle[(start + offset) % 7] = offset % 2
        exceptional = None
    else:
        exceptional = (v - 7) // (k - 3)
        cycle = [special[(j - exceptional) % 7] for j in range(7)]

    colors = list(cycle)
    for i in range(7):
        tri = {cycle[i], cycle[(i + 1) % 7], cycle[(i + 3) % 7]}
        unused = [c for c in palette if c not in tri]
        q = [7 + i * (k - 3) + a for a in range(k - 3)]
        if i != exceptional:
            colors.extend(unused[: k - 3])
        elif u < 7:
            # deleted edge u-v, with v in Q_i
            colors.extend([cycle[u] if w == v else unused.pop(0) for w in q])
        else:
            # deleted edge u-v, both in Q_i
            assigned = {u: unused[0], v: unused[0]}
            rest = iter(unused[1:])
            colors.extend(assigned[w] if w in assigned else next(rest) for w in q)
    assert len(colors) == 7 * (k - 2)
    return tuple(colors)


def check_edge_deletions(k: int) -> None:
    adj = graph(k)
    for edge in all_edges(adj):
        colors = edge_deletion_coloring(k, edge)
        assert all(0 <= c < k - 1 for c in colors)
        assert all(colors[u] != colors[v] for u, v in all_edges(adj) if (u, v) != edge), (k, edge)
    print(f"H_{k}: verified (k−1)-colorings of all {len(all_edges(adj))} edge deletions")


def validate_formulae(k: int) -> None:
    adj = graph(k)
    assert len(adj) == 7 * (k - 2)
    edges = sum(map(len, adj)) // 2
    assert edges == 7 * (k * k - k - 4) // 2, (k, edges)
    assert max(map(len, adj)) == 3 * k - 7
    print(f"H_{k}: |V|={len(adj)}, |E|={edges}, Δ={max(map(len, adj))}")


def exhaustive_h4() -> None:
    k = 4
    adj = graph(k)
    outcomes = Counter()
    cycle_colorings = 0
    for cycle in product(range(k), repeat=7):
        if any(cycle[i] == cycle[(i + 1) % 7] for i in range(7)):
            continue
        available = [tuple(c for c in range(k)
                           if c not in {cycle[i], cycle[(i + 1) % 7],
                                        cycle[(i + 3) % 7]}) for i in range(7)]
        cycle_colorings += 1
        for clique_colors in product(*available):
            colors = cycle + clique_colors
            outcomes[capped_path_count(adj, colors, k)] += 1
    print("H_4 ordered four-colorings: cycle colorings", cycle_colorings,
          "full-path counts capped at two", dict(sorted(outcomes.items())))
    assert outcomes[1] == 0
    assert outcomes[0] == 0


def exhaustive_h5_sorted_cliques() -> None:
    """One representative per permutation of each clique's vertices."""
    k = 5
    adj = graph(k)
    outcomes = Counter()
    for cycle in product(range(k), repeat=7):
        if any(cycle[i] == cycle[(i + 1) % 7] for i in range(7)):
            continue
        available = [list(combinations(
            [c for c in range(k) if c not in
             {cycle[i], cycle[(i + 1) % 7], cycle[(i + 3) % 7]}], k - 3))
                     for i in range(7)]
        for clique_colors in product(*available):
            colors = cycle + tuple(c for pair in clique_colors for c in pair)
            outcomes[capped_path_count(adj, colors, k)] += 1
    print("H_5 sorted-clique ordered five-colorings:",
          dict(sorted(outcomes.items())))
    assert outcomes[1] == 0
    assert outcomes[0] == 0


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--h5", action="store_true", help="also enumerate the H5 case")
    args = parser.parse_args()
    for k in range(4, 21):
        validate_formulae(k)
        check_edge_deletions(k)
    partitions = cycle_partitions()
    qt = Counter(sum(cycle_stats(p)) for p in partitions)
    assert len(partitions) == 162 and qt == {7: 99, 8: 56, 9: 7}
    assert max(cycle_stats(p)[1] for p in partitions) == 6
    special = (0, 1, 0, 2, 1, 0, 1)
    assert [i for i in range(7)
            if len({special[i], special[(i + 1) % 7], special[(i + 3) % 7]}) == 3] == [0]
    print("C7 partitions:", len(partitions), "q+t:", dict(sorted(qt.items())))
    expected = {4: 41160, 5: 832440, 6: 4505760, 7: 9389520,
                8: 8184960, 9: 2540160}
    for k, n in expected.items():
        assert irreducible_count(k, partitions) == n
    print("irreducible counts H4..H9:", expected)
    print("graph6 H4:", graph6(graph(4)))
    print("graph6 H5:", graph6(graph(5)))
    sample = special + tuple(min(set(range(4)) -
                                 {special[i], special[(i + 1) % 7], special[(i + 3) % 7]})
                             for i in range(7))
    print("H4 sample coloring", sample, "exact full paths", exact_path_count(graph(4), sample, 4))
    exhaustive_h4()
    if args.h5:
        exhaustive_h5_sorted_cliques()


if __name__ == "__main__":
    main()
