r"""
regular_closed_form.py -- the aggregate edge-deletion change on regular graphs.

Combining
  * the published value of the Sombor index of an r-regular graph
    (Yurttas Gunes, Ozden Ayna & Cangul, Symmetry 16(2):170 (2024), Theorem 8):
        SO(G) = n r^2 sqrt(2) / 2 = m r sqrt(2),        m = n r / 2,
  * the closed form of the correction term on regular graphs
    (our `C_of_regular`, formalised in Lean):
        C(G) = n r (r-1) (r sqrt2 - sqrt(2 r^2 - 2 r + 1)),
  * our edge-deletion identity  sum_e SO(G-e) = (m-1) SO(G) - C(G)
    (formalised in Lean as `deletion_identity`),
yields the closed form

    sum_e SO(G-e) = m [ (m - 2r + 1) r sqrt2 + 2 (r-1) sqrt(2 r^2 - 2 r + 1) ],

which is what one gets by counting the edge types {r,r} and {r-1,r} of G - e directly.

The script (i) proves the three expressions identical symbolically with sympy, and
(ii) checks every regular graph of the dataset numerically, including Theorem 9 of the
same paper (Nordhaus-Gaddum: SO(G) + SO(complement) = (n sqrt2 / 2)(r^2 + (n-1-r)^2)).
Output: results/regular_closed_form.json
"""

from __future__ import annotations

import gzip
import json
import math
import os
import sys

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from graphlib import from_graph6, degrees, edges_of  # noqa: E402


def nbrs(adj, u: int) -> list[int]:
    """Neighbour list of `u` (graphlib stores adjacency rows as bitmasks)."""
    return [i for i in range(len(adj)) if adj[u] >> i & 1]

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(ROOT, "results")
SQRT2 = math.sqrt(2.0)


def c_kernel(a: int, b: int) -> float:
    return math.hypot(a, b) - math.hypot(a - 1, b)


def sombor(deg, edges) -> float:
    return sum(math.hypot(deg[a], deg[b]) for a, b in edges)


def symbolic_checks() -> dict:
    n, r = sp.symbols("n r", positive=True)
    s2 = sp.sqrt(2)
    m = n * r / 2
    # published Theorem 8, written three ways
    so_direct = m * r * s2
    so_thm8 = n * r ** 2 * s2 / 2
    # our correction term on regular graphs: n * r * (r-1) * c(r,r)
    c_rr = r * s2 - sp.sqrt((r - 1) ** 2 + r ** 2)
    C_reg = n * r * (r - 1) * c_rr
    # aggregate via the identity, and aggregate by counting edge types of G - e
    via_identity = sp.simplify((m - 1) * so_direct - C_reg)
    edge_types = sp.simplify(m * ((m - 2 * r + 1) * r * s2
                                  + 2 * (r - 1) * sp.sqrt((r - 1) ** 2 + r ** 2)))
    diff = sp.simplify(sp.expand(via_identity - edge_types))
    ng_lhs = sp.simplify(so_direct + n * (n - 1 - r) ** 2 * s2 / 2)
    ng_rhs = sp.simplify(n * s2 / 2 * (r ** 2 + (n - 1 - r) ** 2))
    return {
        "sqrt2_times_m_r_equals_n_r2_sqrt2_over_2": sp.simplify(so_direct - so_thm8) == 0,
        "identity_minus_edge_type_count": sp.srepr(diff),
        "identity_equals_edge_type_count": diff == 0,
        "closed_form": sp.srepr(sp.simplify(edge_types)),
        "nordhaus_gaddum_sympy": sp.simplify(ng_lhs - ng_rhs) == 0,
    }


def main() -> int:
    sym = symbolic_checks()
    rows = []
    worst_closed = 0.0
    worst_so = 0.0
    worst_ng = 0.0
    worst_resid = 0.0
    worst_ident = 0.0
    for line in gzip.open(os.path.join(RESULTS, "graphs.jsonl.gz"), "rt"):
        rec = json.loads(line)
        if rec["m"] < 2:
            continue
        adj = from_graph6(rec["g6"])
        deg = degrees(adj)
        r = deg[0]
        if any(d != r for d in deg):          # not regular
            continue
        n, m = rec["n"], rec["m"]
        edges = edges_of(adj)
        so = sombor(deg, edges)
        C = n * r * (r - 1) * c_kernel(r, r)
        # independent aggregate: delete each edge for real and recompute SO from scratch
        sum_so_ge = 0.0
        for a, b in edges:
            d2 = list(deg)
            d2[a] -= 1
            d2[b] -= 1
            sum_so_ge += sum(math.hypot(d2[x], d2[y]) for x, y in edges if (x, y) != (a, b))
        exact = sum(math.hypot(deg[u], deg[v])
                    + sum(c_kernel(deg[u], deg[x]) for x in nbrs(adj, u) if x != v)
                    + sum(c_kernel(deg[v], deg[y]) for y in nbrs(adj, v) if y != u)
                    for u, v in edges)
        closed = m * ((m - 2 * r + 1) * r * SQRT2
                      + 2 * (r - 1) * math.sqrt(2 * r * r - 2 * r + 1))
        thr8 = n * r * r * SQRT2 / 2
        # Nordhaus-Gaddum (Theorem 9): Sombor index of the complement
        comp = [sum(1 << x for x in range(n) if x != u and not (adj[u] >> x & 1))
                for u in range(n)]
        so_comp = sombor(degrees(comp), edges_of(comp))
        ng_err = abs((so + so_comp) - n * SQRT2 / 2 * (r * r + (n - 1 - r) ** 2))
        worst_closed = max(worst_closed, abs(sum_so_ge - closed))
        worst_so = max(worst_so, abs(so - thr8))
        worst_ng = max(worst_ng, ng_err)
        worst_resid = max(worst_resid, abs(exact - (so + C)))
        worst_ident = max(worst_ident, abs(sum_so_ge - ((m - 1) * so - C)))
        rows.append({"g6": rec["g6"], "n": n, "r": r, "m": m,
                     "so": so, "C": C, "sum_delta": exact, "sum_so_ge": sum_so_ge,
                     "closed": closed, "identity": (m - 1) * so - C})
    out = {
        "symbolic": sym,
        "n_regular_graphs_checked": len(rows),
        "max_abs_err_closed_form_vs_direct_edge_deletion": worst_closed,
        "max_abs_err_identity_sum_so_ge": worst_ident,
        "max_abs_err_published_Thm8": worst_so,
        "max_abs_err_Nordhaus_Gaddum_Thm9": worst_ng,
        "max_abs_err_identity_residual_sum_delta": worst_resid,
        "closed_form": "sum_e SO(G-e) = m[(m-2r+1) r sqrt2 + 2(r-1) sqrt(2r^2-2r+1)]",
        "sample": rows[:6],
    }
    with open(os.path.join(RESULTS, "regular_closed_form.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
