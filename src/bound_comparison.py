r"""
bound_comparison.py -- exact aggregate edge-deletion change vs the summed published
per-edge bounds.

Reference
---------
A. Yurttas Gunes, H. Ozden Ayna, I. N. Cangul, "The Effect of Vertex and Edge Removal
on Sombor Index", Symmetry 16(2):170 (2024), doi:10.3390/sym16020170.

That paper proves the *local* (single-edge) change and two per-edge upper bounds:

    Theorem 3 (pendant edge e = uv, v pendant):
        SO(G) - SO(G-e) = sqrt(d_u^2+1) + sum_{w in N(u)\{v}} c(d_u,d_w)
    Theorem 4 (non-pendant edge):
        SO(G) - SO(G-e) = sqrt(d_u^2+d_v^2) + sum_{w in N(u)\{v}} c(d_u,d_w)
                                            + sum_{w in N(v)\{u}} c(d_v,d_w)
    Corollary 4 (pendant edge, support u):
        SO(G) - SO(G-e) <= (d_u - 1)(sqrt2 Delta - A) + sqrt(Delta^2 + 1)
    Corollary 5 (non-pendant edge):
        SO(G) - SO(G-e) <= (m - 1)(sqrt2 Delta - A) + sqrt2 Delta
    with delta = min degree, Delta = max degree, A = sqrt(2 delta^2 - 2 delta + 1).

Our identity (report section 7.1, formalised as `deletion_identity` in Lean) gives the
*exact aggregate* over all edges, with no case distinction:

    sum_e [SO(G) - SO(G-e)] = SO(G) + C(G).

This script compares, for every graph of the test set:
  * `exact`  : sum over edges of the local change, computed edge by edge (Theorem 3/4);
  * `ident`  : our closed form SO(G) + C(G) (residual check against `exact`);
  * `bound`  : sum over edges of the published per-edge bound (Cor. 4 for pendant edges,
               Cor. 5 for non-pendant edges) -- a valid aggregate upper bound;
and records the ratio `bound / exact`.

Test set: all graphs with n <= 8 and m >= 2 (exhaustive) plus all chemical graphs
(connected, max degree <= 4) with n = 9.  Output: results/bound_comparison.json and
results/bound_comparison_examples.csv.
"""

from __future__ import annotations

import gzip
import json
import math
import os
import sys
from statistics import mean, median

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from graphlib import from_graph6, degrees, edges_of  # noqa: E402


def nbrs(adj, u: int) -> list[int]:
    """Neighbour list of `u` (graphlib stores adjacency rows as bitmasks)."""
    return [i for i in range(len(adj)) if adj[u] >> i & 1]

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(ROOT, "results")
SQRT2 = math.sqrt(2.0)


def c_kernel(a: int, b: int) -> float:
    """c(a,b) = sqrt(a^2+b^2) - sqrt((a-1)^2+b^2), the deletion kernel."""
    return math.hypot(a, b) - math.hypot(a - 1, b)


def sombor(deg, edges) -> float:
    return sum(math.hypot(deg[a], deg[b]) for a, b in edges)


def local_change(deg, adj, u, v) -> float:
    """SO(G) - SO(G-uv) (Symmetry 2024, Theorems 3 and 4, in kernel notation)."""
    s = math.hypot(deg[u], deg[v])
    for x in nbrs(adj, u):
        if x != v:
            s += c_kernel(deg[u], deg[x])
    for y in nbrs(adj, v):
        if y != u:
            s += c_kernel(deg[v], deg[y])
    return s


def correction_C(deg, adj) -> float:
    """C(G) = sum_u (d_u - 1) sum_{x in N(u)} c(d_u, d_x)."""
    tot = 0.0
    for u in range(len(adj)):
        du = deg[u]
        if du >= 2:
            tot += (du - 1) * sum(c_kernel(du, deg[x]) for x in nbrs(adj, u))
    return tot


def per_edge_bound(deg, adj, u, v, m, delta, Delta, A) -> float:
    """Published per-edge upper bound: Cor. 4 if the edge is pendant, else Cor. 5."""
    if deg[v] == 1:                      # pendant edge, v pendant, u support
        return (deg[u] - 1) * (SQRT2 * Delta - A) + math.sqrt(Delta * Delta + 1)
    if deg[u] == 1:                      # pendant edge, u pendant, v support
        return (deg[v] - 1) * (SQRT2 * Delta - A) + math.sqrt(Delta * Delta + 1)
    return (m - 1) * (SQRT2 * Delta - A) + SQRT2 * Delta


def is_regular(deg) -> bool:
    return len(set(deg)) == 1


def main() -> int:
    ratios: list[float] = []
    worst: list[dict] = []
    ident_res = 0.0
    n_graphs = 0
    n_violations = 0
    n_regular = 0
    n_strict = 0
    seen_regular: set[tuple[int, int]] = set()
    reg_rows: list[dict] = []

    for line in gzip.open(os.path.join(RESULTS, "graphs.jsonl.gz"), "rt"):
        r = json.loads(line)
        n, m, fl = r["n"], r["m"], r["fl"]
        chemical = bool(fl & 64)
        if m < 2 or not (n <= 8 or (n == 9 and chemical)):
            continue
        adj = from_graph6(r["g6"])
        deg = degrees(adj)
        edges = edges_of(adj)
        if len(edges) != m:
            raise AssertionError("graph6/edge-count mismatch")
        delta, Delta = min(deg), max(deg)
        A = math.sqrt(2 * delta * delta - 2 * delta + 1)
        so = sombor(deg, edges)
        C = correction_C(deg, adj)
        exact = sum(local_change(deg, adj, u, v) for u, v in edges)
        ident = so + C
        bound = sum(per_edge_bound(deg, adj, u, v, m, delta, Delta, A) for u, v in edges)
        n_graphs += 1
        ident_res = max(ident_res, abs(exact - ident))
        if exact > bound + 1e-9:
            n_violations += 1
        if bound > exact + 1e-9:
            n_strict += 1
        ratio = bound / exact
        ratios.append(ratio)
        worst.append({"g6": r["g6"], "n": n, "m": m, "deg_seq": sorted(deg, reverse=True),
                      "exact": exact, "ident": ident, "bound": bound, "ratio": ratio})
        if is_regular(deg):
            n_regular += 1
            seen_regular.add((n, deg[0]))
            reg_rows.append({"g6": r["g6"], "n": n, "r": deg[0], "m": m,
                             "exact": exact, "so": so, "C": C,
                             "closed": m * ((m - 2 * deg[0] + 1) * deg[0] * SQRT2
                                            + 2 * (deg[0] - 1)
                                            * math.sqrt(2 * deg[0] ** 2 - 2 * deg[0] + 1))})

    ratios.sort()
    worst.sort(key=lambda d: -d["ratio"])

    def q(p: float) -> float:
        return ratios[min(len(ratios) - 1, int(p * len(ratios)))]

    out = {
        "reference": "Yurttas Gunes, Ozden Ayna & Cangul, Symmetry 16(2):170 (2024), "
                     "doi:10.3390/sym16020170 (Thm 3-4, Cor 4-5)",
        "test_set": "all graphs n <= 8 with m >= 2 (exhaustive) + chemical graphs n = 9",
        "n_graphs": n_graphs,
        "exact_vs_closed_form_max_residual": ident_res,
        "graphs_where_exact_exceeds_published_bound": n_violations,
        "graphs_where_bound_is_strict": n_strict,
        "ratio_bound_over_exact": {"min": ratios[0], "p25": q(0.25), "median": q(0.5),
                                   "p75": q(0.75), "max": ratios[-1],
                                   "mean": mean(ratios)},
        "n_regular_graphs": n_regular,
        "regular_pairs_n_r": sorted(seen_regular),
        "worst_ratios": worst[:5],
    }
    with open(os.path.join(RESULTS, "bound_comparison.json"), "w") as f:
        json.dump(out, f, indent=1)

    # a few named examples, built directly (not from the dataset)
    examples = []
    for nm, adj in [("K3", [[1, 2], [0, 2], [0, 1]]),
                    ("K4", [[1, 2, 3], [0, 2, 3], [0, 1, 3], [0, 1, 2]]),
                    ("K5", [[j for j in range(5) if j != i] for i in range(5)]),
                    ("P5", [[1], [0, 2], [1, 3], [2, 4], [3]]),
                    ("C5", [[1, 4], [0, 2], [1, 3], [2, 4], [3, 0]]),
                    ("K15_star", [[j for j in range(1, 6)]] + [[0] for _ in range(5)]),
                    ("K23", [[2, 3, 4], [2, 3, 4], [0, 1], [0, 1], [0, 1]])]:
        adj = [sum(1 << x for x in row) for row in adj]
        deg = degrees(adj)
        edges = edges_of(adj)
        m = len(edges)
        delta, Delta = min(deg), max(deg)
        A = math.sqrt(2 * delta * delta - 2 * delta + 1)
        so = sombor(deg, edges)
        C = correction_C(deg, adj)
        exact = sum(local_change(deg, adj, u, v) for u, v in edges)
        bound = sum(per_edge_bound(deg, adj, u, v, m, delta, Delta, A) for u, v in edges)
        examples.append({"graph": nm, "n": len(adj), "m": m, "exact": exact,
                         "closed_form": so + C, "summed_bound": bound,
                         "ratio": bound / exact})
    with open(os.path.join(RESULTS, "bound_comparison_examples.csv"), "w") as f:
        f.write("graph,n,m,exact,closed_form,summed_bound,ratio\n")
        for e in examples:
            f.write(f"{e['graph']},{e['n']},{e['m']},{e['exact']:.6f},"
                    f"{e['closed_form']:.6f},{e['summed_bound']:.6f},{e['ratio']:.4f}\n")

    print(json.dumps(out, indent=1))
    print("\nexamples:")
    for e in examples:
        print(f"  {e['graph']:>9s}  exact={e['exact']:9.4f}  bound={e['summed_bound']:9.4f}"
              f"  ratio={e['ratio']:.3f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
