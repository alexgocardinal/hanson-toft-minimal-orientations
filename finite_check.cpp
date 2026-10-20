// Independent exhaustive check for the finite Hanson--Toft bases.
// Compile: c++ -O3 -std=c++17 irreducible_check.cpp -o irreducible_check
// Usage:   ./irreducible_check 4 9
//
// This checks only colorings with NO color absent from C7 that appears in
// all seven Q_i.  If such a common color exists, remove its seven vertices:
// every full increasing path of H_(k-1) extends injectively to one in H_k.
// Thus induction on k reduces H_5 through H_9 to irreducible cases, once
// ALL H_4 colorings have been ruled out separately (see audit_hanson_toft.py).
// Q_i colors are sorted since Q_i vertices are indistinguishable.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>

using namespace std;

struct Audit {
    int k, n;
    array<int, 49> col{};
    array<array<int, 21>, 49> adj{};
    array<int, 49> deg{};
    array<int, 7> triple_type{};
    array<int, 8> two_prefix{};
    int absent = 0;
    uint64_t cycle_candidates = 0;
    array<uint64_t, 3> histogram{}; // 0, 1, >=2 full paths

    explicit Audit(int kk) : k(kk), n(7 * (kk - 2)) {
        if (kk < 4 || kk > 9) abort();
        for (int i = 0; i < 7; i++) {
            edge(i, (i + 1) % 7);
            for (int a = 0; a < k - 3; a++) {
                int u = 7 + i * (k - 3) + a;
                for (int b = a + 1; b < k - 3; b++)
                    edge(u, 7 + i * (k - 3) + b);
                edge(u, i);
                edge(u, (i + 1) % 7);
                edge(u, (i + 3) % 7);
            }
        }
    }

    void edge(int u, int v) {
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    int path_count_capped() const {
        array<int, 49> dp{};
        array<array<int, 49>, 9> by_rank{};
        array<int, 9> size{};
        for (int v = 0; v < n; v++) by_rank[col[v]][size[col[v]]++] = v;
        for (int t = 0; t < size[0]; t++) dp[by_rank[0][t]] = 1;
        for (int j = 1; j < k; j++) {
            for (int t = 0; t < size[j]; t++) {
                int v = by_rank[j][t], sum = 0;
                for (int a = 0; a < deg[v]; a++) {
                    int u = adj[v][a];
                    if (col[u] == j - 1) sum += dp[u];
                    if (sum >= 2) break;
                }
                dp[v] = min(2, sum);
            }
        }
        int total = 0;
        for (int t = 0; t < size[k - 1]; t++) {
            total += dp[by_rank[k - 1][t]];
            if (total >= 2) return 2;
        }
        return total;
    }

    void fill_clique(int i, int omission) {
        int used = (1 << col[i]) | (1 << col[(i + 1) % 7])
                 | (1 << col[(i + 3) % 7]);
        int w = 7 + i * (k - 3);
        for (int c = 0; c < k; c++)
            if (!(used & (1 << c)) && c != omission) col[w++] = c;
        if (w != 7 + (i + 1) * (k - 3)) abort();
    }

    void cliques(int i, int omitted) {
        if (i == 7) {
            if ((omitted & absent) == absent) {
                int outcome = path_count_capped();
                histogram[outcome]++;
                if (outcome < 2) {
                    cerr << "COUNTEREXAMPLE k=" << k << " colors=";
                    for (int v = 0; v < n; v++) cerr << col[v] << (v + 1 == n ? '\n' : ',');
                    throw logic_error("a coloring has fewer than two full paths");
                }
            }
            return;
        }
        int missing = absent & ~omitted;
        if (__builtin_popcount((unsigned)missing) > two_prefix[7] - two_prefix[i]) return;
        int used = (1 << col[i]) | (1 << col[(i + 1) % 7])
                 | (1 << col[(i + 3) % 7]);
        if (triple_type[i] == 3) {
            fill_clique(i, -1);
            cliques(i + 1, omitted);
        } else {
            for (int omission = 0; omission < k; omission++) {
                if (used & (1 << omission)) continue;
                fill_clique(i, omission);
                cliques(i + 1, omitted | (1 << omission));
            }
        }
    }

    void cycle(int i, int used) {
        if (i < 7) {
            for (int c = 0; c < k; c++) {
                if (i && c == col[i - 1]) continue;
                if (i == 6 && c == col[0]) continue;
                col[i] = c;
                cycle(i + 1, used | (1 << c));
            }
            return;
        }
        absent = ((1 << k) - 1) & ~used;
        two_prefix[0] = 0;
        for (int j = 0; j < 7; j++) {
            int tri = (1 << col[j]) | (1 << col[(j + 1) % 7])
                    | (1 << col[(j + 3) % 7]);
            triple_type[j] = __builtin_popcount((unsigned)tri);
            two_prefix[j + 1] = two_prefix[j] + (triple_type[j] == 2);
        }
        if (__builtin_popcount((unsigned)absent) > two_prefix[7]) return;
        cycle_candidates++;
        cliques(0, 0);
    }

    void run() {
        cycle(0, 0);
        constexpr uint64_t expected_cycles[] = {2184, 16380, 78120, 279930, 112896, 3528};
        constexpr uint64_t expected_irreducible[] = {
            41160, 832440, 4505760, 9389520, 8184960, 2540160
        };
        uint64_t total = histogram[0] + histogram[1] + histogram[2];
        if (cycle_candidates != expected_cycles[k - 4] ||
            total != expected_irreducible[k - 4])
            throw logic_error("enumeration total does not match independent partition formula");
        cout << "H_" << k << ": candidate cycle colorings=" << cycle_candidates
             << ", irreducible sorted-Q colorings=" << total
             << ", path count 0=" << histogram[0]
             << ", path count 1=" << histogram[1]
             << ", path count >=2=" << histogram[2] << '\n';
    }
};

int main(int argc, char **argv) {
    int from = argc >= 2 ? atoi(argv[1]) : 4;
    int to = argc >= 3 ? atoi(argv[2]) : from;
    if (from < 4 || to > 9 || from > to) return 2;
    for (int k = from; k <= to; k++) Audit(k).run();
}
