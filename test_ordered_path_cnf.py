"""Standard-library semantic checks for ordered_path_cnf.py."""

from itertools import combinations, product
import random
import unittest

from ordered_path_cnf import build_hanson_toft, edge_list, encode, hanson_toft_graph
from irreducible_counts import cycle_partitions


def graph(n: int, edges: set[tuple[int, int]]) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(v for v in range(n) if (min(u, v), max(u, v)) in edges)
                 for u in range(n))


class EncodingTests(unittest.TestCase):
    def test_hanson_toft_graphs(self) -> None:
        expected_edges = {4: 28, 5: 56, 6: 91, 7: 133, 8: 182, 9: 238}
        for k, m in expected_edges.items():
            adj = hanson_toft_graph(k)
            self.assertEqual(len(adj), 7 * (k - 2))
            self.assertEqual(len(edge_list(adj)), m)
            self.assertEqual(max(map(len, adj)), 3 * k - 7)
            self.assertEqual(adj, tuple(tuple(u for u, row in enumerate(adj) if v in row)
                                        for v in range(len(adj))))

    def test_all_small_graphs_and_colorings(self) -> None:
        """Exhaust all 64 graphs and all 81 three-colorings on four vertices."""
        potential = list(combinations(range(4), 2))
        for mask in range(1 << len(potential)):
            es = {e for i, e in enumerate(potential) if mask & (1 << i)}
            model = encode(graph(4, es), 3)
            for colors in product(range(3), repeat=4):
                proper = all(colors[u] != colors[v] for u, v in es)
                expected = proper and model.full_path_count(colors, cap=2) == 1
                assignment = model.complete_assignment(colors)
                self.assertEqual(model.satisfies(assignment), expected,
                                 msg=f"edges={es}, coloring={colors}")
                counts = [int(c == 0) for c in colors]
                for j in range(3):
                    if j:
                        counts = [sum(counts[u] for u in model.adj[v])
                                  if colors[v] == j else 0 for v in range(4)]
                    for v in range(4):
                        self.assertEqual(assignment[model.reach[v][j]], counts[v] > 0)
                        self.assertEqual(assignment[model.multiple[v][j]], counts[v] > 1)

    def test_positive_and_negative_controls(self) -> None:
        complete = graph(4, set(combinations(range(4), 2)))
        model = encode(complete, 4)
        self.assertEqual(model.full_path_count((0, 1, 2, 3)), 1)
        self.assertTrue(model.satisfies(model.complete_assignment((0, 1, 2, 3))))

        diamond = graph(4, {(0, 1), (0, 2), (1, 3), (2, 3)})
        model = encode(diamond, 3)
        colors = (0, 1, 1, 2)
        self.assertEqual(model.full_path_count(colors), 2)
        values = model.complete_assignment(colors)
        self.assertTrue(values[model.multiple[3][2]])
        self.assertFalse(model.satisfies(values))

        h4 = build_hanson_toft(4, symmetry=False)
        colors = (0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 0, 2, 2, 2)
        self.assertEqual(h4.full_path_count(colors), 4)
        self.assertFalse(h4.satisfies(h4.complete_assignment(colors)))

    def test_symmetry_restrictions(self) -> None:
        for k in range(4, 10):
            model = build_hanson_toft(k, symmetry=True)
            self.assertEqual(len(model.adj), 7 * (k - 2))
            self.assertTrue(model.cnf.variable_count > len(model.adj) * k)
        with self.assertRaises(ValueError):
            encode(graph(4, set()), 4, symmetry=True)

    def test_symmetry_normalization_preserves_path_count(self) -> None:
        rng = random.Random(1729)
        partitions = list(cycle_partitions())
        for k in range(4, 10):
            model = build_hanson_toft(k, symmetry=False)
            admissible = [p for p in partitions if max(p) < k]
            for _ in range(60):
                pattern = rng.choice(admissible)
                palette = rng.sample(range(k), max(pattern) + 1)
                cycle = [palette[x] for x in pattern]
                colors = cycle[:]
                for i in range(7):
                    triple = {cycle[i], cycle[(i + 1) % 7], cycle[(i + 3) % 7]}
                    colors.extend(rng.sample([j for j in range(k) if j not in triple],
                                              k - 3))
                original_count = model.full_path_count(colors)
                if min(colors[:7]) > (k - 1) // 2:
                    colors = [k - 1 - c for c in colors]
                shift = colors[:7].index(min(colors[:7]))
                normalized = [colors[(i + shift) % 7] for i in range(7)]
                for i in range(7):
                    source = (i + shift) % 7
                    a = 7 + source * (k - 3)
                    normalized.extend(sorted(colors[a:a + k - 3]))
                self.assertEqual(original_count, model.full_path_count(normalized))
                self.assertEqual(normalized[0], min(normalized[:7]))
                self.assertLessEqual(normalized[0], (k - 1) // 2)
                for i in range(7):
                    a = 7 + i * (k - 3)
                    self.assertEqual(normalized[a:a + k - 3],
                                     sorted(normalized[a:a + k - 3]))


if __name__ == "__main__":
    unittest.main()
