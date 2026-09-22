r"""
naive_identity_check.py -- exhaustive characterisation of the "linear scaling" identity

        sum_{e in E} SO(G - e)  =?=  (m - 1) SO(G)                                (naive)

for all graphs with n <= 9 and m >= 2 (288,249 graphs).

The identity is *not* taken from the literature: it is the natural guess that the index
scales linearly with the number of edges (it is exact for the trivial index T = m), and
it appears in this project's task statement.  The edge-wise deletion formula it would
have to follow from is published (Symmetry 16(2):170 (2024), Thm 3-4); summing that
formula gives  sum_e SO(G-e) = (m-1) SO(G) - C(G), so the naive form can only hold when
C(G) = 0, which by the star/zero theorems means that G is a matching.

This script verifies the resulting prediction exactly:
  * naive holds  <=>  every degree <= 1  (G is a matching),
  * the number of graphs where it holds is 12, and they are precisely the matchings with
    at least two edges, (n, k) in {(4,2),(5,2),(6,2),(6,3),(7,2),(7,3),(8,2),(8,3),(8,4),
    (9,2),(9,3),(9,4)},
  * every connected graph with n >= 3 fails.

For speed the per-edge change is evaluated with the kernel formula
Delta_e = sqrt(d_u^2+d_v^2) + sum_{x in N(u)\v} c(d_u,d_x) + sum_{y in N(v)\u} c(d_v,d_y)
(which the Symmetry paper proves and which is verified independently in
`results/sombor_identity_check.csv`); a random subsample is additionally checked by
deleting each edge for real and recomputing SO(G-e) from scratch.
Output: results/naive_identity_characterization.json
"""

from __future__ import annotations

import gzip
import json
import math
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from graphlib import from_graph6, degrees, edges_of  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(ROOT, "results")


def nbrs(adj, u: int) -> list[int]:
    return [i for i in range(len(adj)) if adj[u] >> i & 1]


def c_kernel(a: int, b: int) -> float:
    return math.hypot(a, b) - math.hypot(a - 1, b)


def sombor_from_deg(deg, edges) -> float:
    return sum(math.hypot(deg[a], deg[b]) for a, b in edges)


def main() -> int:
    rng = random.Random(20240201)
    n_graphs = n_hold = 0
    fails_by_n: dict[int, int] = {}
    hold_but_not_matching = not_hold_but_matching = 0
    connected_failures = connected_total = 0
    witnesses: list[dict] = []
    cross_checked = cross_mismatch = 0
    worst_gap = 0.0

    for line in gzip.open(os.path.join(RESULTS, "graphs.jsonl.gz"), "rt"):
        rec = json.loads(line)
        m = rec["m"]
        if m < 2:
            continue
        adj = from_graph6(rec["g6"])
        deg = degrees(adj)
        edges = edges_of(adj)
        so = sombor_from_deg(deg, edges)
        agg = 0.0
        for u, v in edges:
            agg += math.hypot(deg[u], deg[v])
            agg += sum(c_kernel(deg[u], deg[x]) for x in nbrs(adj, u) if x != v)
            agg += sum(c_kernel(deg[v], deg[y]) for y in nbrs(adj, v) if y != u)
        sum_so_ge = m * so - agg          # sum_e SO(G-e) = m SO(G) - sum_e Delta_e
        naive = abs(sum_so_ge - (m - 1) * so) <= 1e-7
        matching = all(d <= 1 for d in deg)
        n_graphs += 1
        if naive:
            n_hold += 1
            witnesses.append({"g6": rec["g6"], "n": rec["n"], "m": m,
                              "deg_seq": sorted(deg, reverse=True)})
            if not matching:
                hold_but_not_matching += 1
        elif matching:
            not_hold_but_matching += 1
        if rec["fl"] & 1:                      # connected
            connected_total += 1
            if not naive:
                connected_failures += 1
        worst_gap = max(worst_gap,
                        abs(sum_so_ge - (m - 1) * so) / max((m - 1) * so, 1e-12))
        fails_by_n[rec["n"]] = fails_by_n.get(rec["n"], 0) + (0 if naive else 1)
        if n_graphs % 4000 == 0:               # random independent cross-check
            d2 = list(deg)
            e0 = rng.choice(edges)
            d2[e0[0]] -= 1
            d2[e0[1]] -= 1
            real = so - sombor_from_deg(d2, [e for e in edges if e != e0])
            kern = (math.hypot(deg[e0[0]], deg[e0[1]])
                    + sum(c_kernel(deg[e0[0]], deg[x]) for x in nbrs(adj, e0[0]) if x != e0[1])
                    + sum(c_kernel(deg[e0[1]], deg[y]) for y in nbrs(adj, e0[1]) if y != e0[0]))
            cross_checked += 1
            if abs(real - kern) > 1e-9:
                cross_mismatch += 1

    out = {
        "question": "sum_e SO(G-e) = (m-1) SO(G)  (the 'linear scaling' guess)",
        "provenance": "natural guess made in this project's task statement; NOT a claim of "
                      "Symmetry 16(2):170 (2024) or of any other source we could find "
                      "(see refs/symmetry-2024-mapping.md)",
        "prediction": "holds iff C(G)=0 iff every degree <= 1 (G is a matching)",
        "test_set": "all graphs n <= 9 with m >= 2",
        "n_graphs": n_graphs,
        "n_graphs_where_naive_holds": n_hold,
        "holds_but_not_matching": hold_but_not_matching,
        "matching_but_does_not_hold": not_hold_but_matching,
        "connected_graphs": connected_total,
        "connected_graphs_where_naive_fails": connected_failures,
        "witnesses": witnesses,
        "max_relative_gap": worst_gap,
        "naive_failures": n_graphs - n_hold,
        "naive_failures_by_n": {str(k): v for k, v in sorted(fails_by_n.items())},
        "independent_cross_checks": cross_checked,
        "independent_cross_check_mismatches": cross_mismatch,
        "prediction_confirmed": (hold_but_not_matching == 0 and not_hold_but_matching == 0
                                 and connected_failures == connected_total),
    }
    with open(os.path.join(RESULTS, "naive_identity_characterization.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != "witnesses"}, indent=1))
    print("witnesses:", [(w["n"], w["m"]) for w in witnesses])
    return 0


if __name__ == "__main__":
    sys.exit(main())
