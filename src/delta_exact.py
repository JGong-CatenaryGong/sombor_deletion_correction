"""
delta_exact.py -- is Delta_e a function of the edge degree-type?

Delta_e depends on the deleted edge uv only through

    (a, b, A, B)   a = d_u, b = d_v, A = degrees of N(u)\\{v}, B = degrees of N(v)\\{u}

called here the *edge configuration*:

    Delta(a,b,A,B) = sqrt(a^2+b^2) + sum_{x in A} c(a,x) + sum_{y in B} c(b,y),
    c(a,x) = sqrt(a^2+x^2) - sqrt((a-1)^2+x^2).

The low-precision scan in sombor_analysis.py quantises at 1e-9 and produced a few
'apparent' coincidences between different edge types.  This script re-examines
them at 60 significant digits and checks symbolically (sympy) whether the
coincidences are exact algebraic identities or mere floating point artefacts.

Outputs
  results/delta_configurations.csv   occurring configurations and their exact Delta
  results/delta_coincidences.json    cross-type coincidences (high precision)
"""

from __future__ import annotations

import csv
import gzip
import json
import math
import os
import sys
from collections import defaultdict

import sympy as sp

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import graphlib as gl

PREC = 60


def delta_expr(a: int, b: int, A, B):
    e = sp.sqrt(a * a + b * b)
    for x in A:
        e += sp.sqrt(a * a + x * x) - sp.sqrt((a - 1) ** 2 + x * x)
    for y in B:
        e += sp.sqrt(b * b + y * y) - sp.sqrt((b - 1) ** 2 + y * y)
    return e


def main():
    ap = __import__("argparse").ArgumentParser()
    ap.add_argument("--graphs", default="results/graphs.jsonl.gz")
    ap.add_argument("--maxdeg", type=int, default=8)
    args = ap.parse_args()

    configs = defaultdict(int)  # (a,b,A,B) -> occurrences
    n_graphs = 0
    with gzip.open(args.graphs, "rt") as f:
        for line in f:
            g6 = json.loads(line)["g6"]
            adj = gl.from_graph6(g6)
            deg = gl.degrees(adj)
            n_graphs += 1
            for u, v in gl.edges_of(adj):
                a, b = deg[u], deg[v]
                A = tuple(sorted(deg[x] for x in _nbrs(adj[u] & ~(1 << v))))
                B = tuple(sorted(deg[y] for y in _nbrs(adj[v] & ~(1 << u))))
                configs[(a, b, A, B)] += 1
    print(f"scanned {n_graphs} graphs, {len(configs)} distinct edge configurations", flush=True)

    rows = []
    by_value = defaultdict(list)
    for (a, b, A, B), cnt in configs.items():
        e = delta_expr(a, b, A, B)
        val = sp.N(e, PREC)
        key = sp.N(e, 30)
        rows.append({
            "a": a, "b": b, "A": list(A), "B": list(B), "count": cnt,
            "delta_60": sp.sstr(val),
        })
        by_value[str(key)].append((a, b, A, B, val))

    shared = {k: v for k, v in by_value.items() if len({(t[0], t[1]) for t in v}) > 1}
    print(f"distinct Delta values: {len(by_value)}; shared by >1 edge type: {len(shared)}", flush=True)
    coincidences = []
    for k, v in sorted(shared.items()):
        types = sorted({(t[0], t[1]) for t in v})
        exact = []
        base = v[0]
        for other in v[1:]:
            d = sp.simplify(delta_expr(*base[:4]) - delta_expr(*other[:4]))
            exact.append({"configs": [list(base[:4]), list(other[:4])], "difference": sp.sstr(d),
                          "is_exact_zero": d == 0})
        allzero = all(x["is_exact_zero"] for x in exact)
        coincidences.append({
            "delta_30": k, "types": types, "n_configs": len(v),
            "configs": [list(t[:4]) for t in v][:8],
            "exact_identity": allzero,
            "checks": exact[:4],
        })
        print(f"  Delta={sp.N(sp.Float(k), 20)} types={types} configs={len(v)} exact_identity={allzero}", flush=True)

    with open("results/delta_configurations.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["a", "b", "A", "B", "count", "delta_60"])
        w.writeheader()
        for r in sorted(rows, key=lambda r: (r["a"], r["b"], r["A"], r["B"])):
            w.writerow({**r, "A": ";".join(map(str, r["A"])), "B": ";".join(map(str, r["B"]))})
    with open("results/delta_coincidences.json", "w") as f:
        json.dump({"n_distinct_configurations": len(configs),
                   "n_distinct_delta_values": len(by_value),
                   "n_shared_by_multiple_types": len(shared),
                   "coincidences": coincidences}, f, indent=1)
    print("wrote results/delta_configurations.csv, results/delta_coincidences.json")


def _nbrs(mask: int):
    out = []
    while mask:
        b = mask & -mask
        out.append(b.bit_length() - 1)
        mask ^= b
    return out


if __name__ == "__main__":
    main()
