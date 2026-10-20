"""Independent DIMACS encoding of exactly one full increasing path in H_k.

Requires only the Python standard library.  The vertex order is x_0,...,x_6,
then Q_0,...,Q_6 in clique order.  T_i = {x_i,x_(i+1),x_(i+3)}.

Every Tseitin gate is an equivalence, so supplying the vertex colors uniquely
determines every auxiliary Boolean value.  `complete_assignment` computes this
assignment for direct semantic checks without calling a SAT solver.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass, field
from itertools import combinations
from pathlib import Path
from typing import Iterable


def hanson_toft_graph(k: int) -> tuple[tuple[int, ...], ...]:
    if k < 4:
        raise ValueError("k must be at least 4")
    n = 7 * (k - 2)
    adj = [set() for _ in range(n)]

    def edge(a: int, b: int) -> None:
        if a == b:
            raise AssertionError("loop")
        adj[a].add(b)
        adj[b].add(a)

    for i in range(7):
        edge(i, (i + 1) % 7)
        triple = (i, (i + 1) % 7, (i + 3) % 7)
        clique = tuple(7 + i * (k - 3) + a for a in range(k - 3))
        for v in clique:
            for x in triple:
                edge(v, x)
        for u, v in combinations(clique, 2):
            edge(u, v)
    return tuple(tuple(sorted(row)) for row in adj)


def edge_list(adj: tuple[tuple[int, ...], ...]) -> list[tuple[int, int]]:
    return [(u, v) for u, row in enumerate(adj) for v in row if u < v]


@dataclass
class CNF:
    clauses: list[tuple[int, ...]] = field(default_factory=list)
    names: list[str] = field(default_factory=lambda: ["unused-zero-index"])
    gates: list[tuple[int, str, tuple[int, ...]]] = field(default_factory=list)

    def variable(self, name: str) -> int:
        self.names.append(name)
        return len(self.names) - 1

    @property
    def variable_count(self) -> int:
        return len(self.names) - 1

    def add(self, *lits: int) -> None:
        if any(not lit or abs(lit) > self.variable_count for lit in lits):
            raise ValueError("invalid literal")
        self.clauses.append(tuple(lits))

    def or_gate(self, name: str, inputs: Iterable[int]) -> int:
        xs = tuple(inputs)
        y = self.variable(name)
        self.add(-y, *xs)
        for x in xs:
            self.add(-x, y)
        self.gates.append((y, "or", xs))
        return y

    def and_gate(self, name: str, inputs: Iterable[int]) -> int:
        xs = tuple(inputs)
        y = self.variable(name)
        for x in xs:
            self.add(-y, x)
        self.add(y, *(-x for x in xs))
        self.gates.append((y, "and", xs))
        return y


@dataclass
class Encoding:
    cnf: CNF
    adj: tuple[tuple[int, ...], ...]
    k: int
    colors: list[list[int]]
    reach: list[list[int]]
    multiple: list[list[int]]
    symmetry: bool

    def complete_assignment(self, vertex_colors: Iterable[int]) -> list[bool]:
        """The sole possible auxiliary assignment for a prescribed coloring."""
        coloring = tuple(vertex_colors)
        if len(coloring) != len(self.adj):
            raise ValueError("wrong number of vertices")
        if any(c not in range(self.k) for c in coloring):
            raise ValueError("color outside the palette")
        values = [False] * (self.cnf.variable_count + 1)
        for v, c in enumerate(coloring):
            values[self.colors[v][c]] = True
        for y, op, xs in self.cnf.gates:
            if op == "or":
                values[y] = any(values[x] for x in xs)
            elif op == "and":
                values[y] = all(values[x] for x in xs)
            else:
                raise AssertionError(op)
        return values

    def satisfies(self, values: list[bool]) -> bool:
        if len(values) != self.cnf.variable_count + 1:
            raise ValueError("wrong number of Boolean values")
        return all(any(values[x] if x > 0 else not values[-x] for x in clause)
                   for clause in self.cnf.clauses)

    def full_path_count(self, coloring: Iterable[int], cap: int | None = None) -> int:
        """Independent integer path recurrence, for checking the Boolean model."""
        cs = tuple(coloring)
        prev = [int(c == 0) for c in cs]
        for j in range(1, self.k):
            nxt = [0] * len(cs)
            for v, c in enumerate(cs):
                if c == j:
                    nxt[v] = sum(prev[u] for u in self.adj[v])
                    if cap is not None:
                        nxt[v] = min(cap, nxt[v])
            prev = nxt
        out = sum(prev)
        return out if cap is None else min(cap, out)

    def write_dimacs(self, output: str | Path) -> str:
        """Write exact CNF, returning SHA-256 of the resulting bytes."""
        output = Path(output)
        digest = hashlib.sha256()
        with output.open("wb") as f:
            def line(s: str) -> None:
                b = s.encode("ascii")
                f.write(b)
                digest.update(b)
            line(f"c H_{self.k}; x_i=0..6; Q_i[a]=7+i*(k-3)+a\n")
            line(f"c symmetry={'rotation reversal clique-sort' if self.symmetry else 'none'}\n")
            line(f"p cnf {self.cnf.variable_count} {len(self.cnf.clauses)}\n")
            for clause in self.cnf.clauses:
                line(" ".join(map(str, clause)) + " 0\n")
        return digest.hexdigest()


def encode(adj: tuple[tuple[int, ...], ...], k: int, symmetry: bool = False) -> Encoding:
    """Satisfiable iff a proper ordered k-coloring has exactly one full path.

    When `symmetry` is set the graph must be H_k.  Rotations of its 7-cycle,
    reversal of all color ranks, and permutations inside each clique make the
    extra restrictions complete for the existence question.
    """
    if symmetry and adj != hanson_toft_graph(k):
        raise ValueError("symmetry constraints apply only to the canonical H_k")
    n = len(adj)
    cnf = CNF()
    color = [[cnf.variable(f"C({v},{j})") for j in range(k)] for v in range(n)]
    for v in range(n):
        cnf.add(*color[v])
        for a, b in combinations(range(k), 2):
            cnf.add(-color[v][a], -color[v][b])
    for u, v in edge_list(adj):
        for j in range(k):
            cnf.add(-color[u][j], -color[v][j])

    if symmetry:
        for i in range(7):
            clique = [7 + i * (k - 3) + a for a in range(k - 3)]
            for u, v in zip(clique, clique[1:]):
                for a in range(k):
                    for b in range(a + 1):
                        cnf.add(-color[u][a], -color[v][b])
        for v in range(1, 7):
            for a in range(k):
                for b in range(a):
                    cnf.add(-color[0][a], -color[v][b])
        for j in range((k - 1) // 2 + 1, k):
            cnf.add(-color[0][j])

    reach = [[0] * k for _ in range(n)]
    multiple = [[0] * k for _ in range(n)]
    for v in range(n):
        reach[v][0] = cnf.and_gate(f"R({v},0)", (color[v][0],))
        multiple[v][0] = cnf.or_gate(f"M({v},0)", ())
    for j in range(1, k):
        for v, row in enumerate(adj):
            predecessor = cnf.or_gate(f"some_R({v},{j})", (reach[u][j - 1] for u in row))
            reach[v][j] = cnf.and_gate(f"R({v},{j})", (color[v][j], predecessor))
            pairs = [cnf.and_gate(f"pair_R({v},{j},{u},{w})",
                                  (reach[u][j - 1], reach[w][j - 1]))
                     for u, w in combinations(row, 2)]
            several = cnf.or_gate(f"several({v},{j})",
                                  [*(multiple[u][j - 1] for u in row), *pairs])
            multiple[v][j] = cnf.and_gate(f"M({v},{j})", (color[v][j], several))

    terminal = [reach[v][k - 1] for v in range(n)]
    cnf.add(*terminal)
    for a, b in combinations(terminal, 2):
        cnf.add(-a, -b)
    for v in range(n):
        cnf.add(-multiple[v][k - 1])
    return Encoding(cnf, adj, k, color, reach, multiple, symmetry)


def build_hanson_toft(k: int, symmetry: bool = True) -> Encoding:
    return encode(hanson_toft_graph(k), k, symmetry)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("k", type=int)
    parser.add_argument("output", type=Path, help="DIMACS output path")
    parser.add_argument("--no-symmetry", action="store_true")
    args = parser.parse_args()
    model = build_hanson_toft(args.k, not args.no_symmetry)
    sha = model.write_dimacs(args.output)
    print(json.dumps(dict(k=args.k, vertices=len(model.adj),
                          edges=len(edge_list(model.adj)),
                          variables=model.cnf.variable_count,
                          clauses=len(model.cnf.clauses),
                          symmetry=model.symmetry, sha256=sha), sort_keys=True))


if __name__ == "__main__":
    main()
