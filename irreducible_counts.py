"""Count the exact finite search space left by the universal-color reduction.

These counts do not assert the path theorem. They are a sizing and coverage
check for a possible exhaustive finite proof: H4 needs every sorted-clique
coloring; H5..H9 need only colorings without an absent-cycle color occurring
in every attachment clique, once smaller k is established.
"""

from collections import Counter
from math import comb, factorial


def cycle_partitions():
    """Every proper C7 color partition, in restricted-growth form."""
    def rec(sequence, greatest):
        if len(sequence) == 7:
            if sequence[-1] != sequence[0]:
                yield tuple(sequence)
            return
        for color in range(greatest + 2):
            if color != sequence[-1]:
                sequence.append(color)
                yield from rec(sequence, max(color, greatest))
                sequence.pop()
    yield from rec([0], 0)


def cycle_stats(sequence):
    q = max(sequence) + 1
    t = sum(len({sequence[i], sequence[(i + 1) % 7],
                 sequence[(i + 3) % 7]}) == 2 for i in range(7))
    return q, t


def onto_omission_count(k: int, q: int, t: int) -> int:
    """Maps from t two-color triples to their omitted ranks covering all k-q
    ranks missing from the cycle; each triple has k-2 possible omissions.
    Inclusion-exclusion counts maps onto the designated k-q ranks, allowing
    other omissions too.
    """
    n = k - q
    if n < 0:
        return 0
    return sum((-1) ** j * comb(n, j) * (k - 2 - j) ** t
               for j in range(n + 1))


def counts():
    patterns = Counter(map(cycle_stats, cycle_partitions()))
    assert sum(patterns.values()) == 162
    assert max(q + t for q, t in patterns) == 9
    print("cycle partition counts by (q,t):", sorted(patterns.items()))
    for k in range(4, 10):
        total = irreducible = 0
        for (q, t), mult in patterns.items():
            if q > k:
                continue
            ordered_cycle_colors = factorial(k) // factorial(k - q)
            total += mult * ordered_cycle_colors * (k - 2) ** t
            irreducible += mult * ordered_cycle_colors * onto_omission_count(k, q, t)
        print(f"k={k}: all={total:,}; irreducible={irreducible:,}; "
              f"irreducible/rotation={irreducible // 7:,}")
        assert irreducible % 7 == 0
    print("Use all, rather than irreducible, at k=4 (H3 is not a proved base).")


if __name__ == "__main__":
    counts()
