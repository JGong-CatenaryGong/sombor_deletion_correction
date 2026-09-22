r"""
general_identity.py -- the Sombor correction is an instance of a general theorem.

Theorem (general edge-deletion identity).
Let T_f(G) = sum_{uv in E(G)} f(d_u, d_v) be an edge-additive degree-based index
with symmetric f.  Put c_f(a,b) = f(a,b) - f(a-1,b) and

    C_f(G) = sum_{u in V} (d_u - 1) * sum_{x in N(u)} c_f(d_u, d_x)
           = sum_{uv in E} [ (d_u-1) c_f(d_u,d_v) + (d_v-1) c_f(d_v,d_u) ].

Then
    (i)   Delta_e := T_f(G) - T_f(G-e)
          = f(d_u,d_v) + sum_{x in N(u)\{v}} c_f(d_u,d_x) + sum_{y in N(v)\{u}} c_f(d_v,d_y),
    (ii)  sum_{e in E} T_f(G-e) = (m-1) T_f(G) - C_f(G).

Proof.  Deleting uv changes exactly the terms of T_f that are incident with u or
with v, which gives (i).  Summing (i) over all e in E, the term c_f(d_u,d_x) of
the ordered pair (u,x) occurs once for every edge at u different from ux, i.e.
d_u - 1 times, while each edge uv contributes f(d_u,d_v) exactly once (that sum
is T_f(G)).  Hence sum_e Delta_e = T_f(G) + C_f(G); and since
sum_e Delta_e = m T_f(G) - sum_e T_f(G-e), (ii) follows.  QED

Consequences verified here for many f:
  * the 'naive' identity sum_e T_f(G-e) = (m-1) T_f(G) holds iff C_f == 0, i.e.
    iff f(a,b) = f(a-1,b) for all a >= 2 -- for a symmetric f this forces f to be
    independent of the degrees, i.e. the trivial index T = m;
  * C_f depends on G only through the multiset of degree pairs of its edges.

Vertex-degree (non edge-additive) indices admit analogous, equally elementary
closed forms, which are verified here as well:
    sum_e M1(G-e) = (m-2) M1(G) + 2m,      M1 = sum_v d_v^2
    sum_e F(G-e)  = (m-3) F(G) + 3 M1(G) - 2m,   F = sum_v d_v^3

Outputs
  results/general_identity.csv    per index: failures of (ii), of the naive form,
                                  number of graphs checked, max error, C_f vs edge types
  results/general_identity.json   summary
"""

from __future__ import annotations

import argparse
import csv
import gzip
import json
import math
import multiprocessing as mp
import os
import sys
import time
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import graphlib as gl

FLAG_CHEMICAL = 64


def f_sombor(a, b):
    return math.sqrt(a * a + b * b)


def f_sombor_inv(a, b):
    return 1.0 / math.sqrt(a * a + b * b)


def f_sombor_sq(a, b):
    return float(a * a + b * b)


def f_randic(a, b):
    return 1.0 / math.sqrt(a * b)


def f_abc(a, b):
    x = (a + b - 2) / (a * b)
    return math.sqrt(x) if x > 0 else 0.0


def f_m2(a, b):
    return float(a * b)


def f_harmonic(a, b):
    return 2.0 / (a + b)


def f_ga(a, b):
    return 2.0 * math.sqrt(a * b) / (a + b)


def f_sum_conn(a, b):
    return 1.0 / math.sqrt(a + b)


def f_isi(a, b):
    return a * b / (a + b)


def f_az(a, b):
    x = a + b - 2
    return (a * b / x) ** 3 if x > 0 else 0.0


def f_trivial(a, b):
    return 1.0  # T = m, the only index with C_f == 0


EDGE_INDICES = {
    "sombor": f_sombor,
    "sombor_inv": f_sombor_inv,
    "sombor_sq": f_sombor_sq,
    "randic": f_randic,
    "abc": f_abc,
    "m2": f_m2,
    "harmonic": f_harmonic,
    "ga": f_ga,
    "sum_conn": f_sum_conn,
    "isi": f_isi,
    "az": f_az,
    "trivial(m)": f_trivial,
}


def analyse(g6: str) -> dict:
    adj = gl.from_graph6(g6)
    n = len(adj)
    deg = gl.degrees(adj)
    edges = gl.edges_of(adj)
    m = len(edges)
    out = {"g6": g6, "n": n, "m": m, "et": tuple(sorted((min(deg[u], deg[v]), max(deg[u], deg[v])) for u, v in edges))}
    # vertex-degree based closed forms
    m1 = sum(d * d for d in deg)
    f3 = sum(d ** 3 for d in deg)
    s_m1 = 0.0
    s_f3 = 0.0
    for u, v in edges:
        c = list(adj)
        c[u] &= ~(1 << v)
        c[v] &= ~(1 << u)
        d2 = gl.degrees(tuple(c))
        s_m1 += sum(x * x for x in d2)
        s_f3 += sum(x ** 3 for x in d2)
    out["M1_sum"] = s_m1
    out["M1_formula"] = (m - 2) * m1 + 2 * m if m >= 1 else 0.0
    out["F_sum"] = s_f3
    out["F_formula"] = (m - 3) * f3 + 3 * m1 - 2 * m
    # edge-additive indices
    for name, f in EDGE_INDICES.items():
        TG = sum(f(deg[u], deg[v]) for u, v in edges)
        s_card = 0.0
        for u, v in edges:
            c = list(adj)
            c[u] &= ~(1 << v)
            c[v] &= ~(1 << u)
            d2 = gl.degrees(tuple(c))
            s_card += sum(f(d2[x], d2[y]) for x, y in gl.edges_of(tuple(c)))
        C = 0.0
        for u, v in edges:
            if deg[u] >= 2:
                C += (deg[u] - 1) * (f(deg[u], deg[v]) - f(deg[u] - 1, deg[v]))
            if deg[v] >= 2:
                C += (deg[v] - 1) * (f(deg[v], deg[u]) - f(deg[v] - 1, deg[u]))
        out[name] = {
            "T": TG,
            "sum_cards": s_card,
            "corrected": (m - 1) * TG - C if m >= 1 else 0.0,
            "naive": (m - 1) * TG if m >= 1 else 0.0,
            "C": C,
        }
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graphs", default="results/graphs.jsonl.gz")
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 4) - 2))
    args = ap.parse_args()

    t0 = time.time()
    recs = []
    with gzip.open(args.graphs, "rt") as fh:
        for line in fh:
            r = json.loads(line)
            if r["n"] <= 8 or (r["fl"] & FLAG_CHEMICAL):
                recs.append(r)
    print(f"{len(recs)} graphs (n<=8 plus all chemical n=9)", flush=True)

    stat = {name: {"naive_fail": 0, "corr_fail": 0, "max_err": 0.0, "n_m_ge2": 0,
                   "shared_delta_types": 0, "max_naive_rel": 0.0} for name in EDGE_INDICES}
    et_to_C = {name: defaultdict(set) for name in EDGE_INDICES}
    m1_fail = f3_fail = 0
    m1_err = f3_err = 0.0
    done = 0
    with mp.Pool(args.workers) as pool:
        for r in pool.imap(analyse, [x["g6"] for x in recs], chunksize=64):
            done += 1
            if r["m"] >= 2:
                m1_fail += abs(r["M1_sum"] - r["M1_formula"]) > 1e-7
                f3_fail += abs(r["F_sum"] - r["F_formula"]) > 1e-7
                m1_err = max(m1_err, abs(r["M1_sum"] - r["M1_formula"]))
                f3_err = max(f3_err, abs(r["F_sum"] - r["F_formula"]))
            for name in EDGE_INDICES:
                d = r[name]
                st = stat[name]
                et_to_C[name][r["et"]].add(round(d["C"], 9))
                if r["m"] < 2:
                    continue
                st["n_m_ge2"] += 1
                err = abs(d["sum_cards"] - d["corrected"])
                st["max_err"] = max(st["max_err"], err)
                if err > 1e-7:
                    st["corr_fail"] += 1
                if abs(d["sum_cards"] - d["naive"]) > 1e-7:
                    st["naive_fail"] += 1
                if d["naive"]:
                    st["max_naive_rel"] = max(st["max_naive_rel"],
                                              abs(d["sum_cards"] - d["naive"]) / abs(d["naive"]))
            if done % 5000 == 0:
                print(f"  {done}/{len(recs)}", flush=True)

    rows = []
    for name in EDGE_INDICES:
        st = stat[name]
        bad = sum(1 for k, v in et_to_C[name].items() if len(v) > 1)
        rows.append({
            "index": name,
            "graphs_checked_m>=2": st["n_m_ge2"],
            "corrected_identity_failures": st["corr_fail"],
            "naive_identity_failures": st["naive_fail"],
            "max_abs_error_corrected": f'{st["max_err"]:.3e}',
            "max_rel_error_naive": f'{st["max_naive_rel"]:.6f}',
            "edge_type_multisets": len(et_to_C[name]),
            "C_f_inconsistent_with_edge_types": bad,
        })
    with open("results/general_identity.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    for r in rows:
        print(r, flush=True)
    print(f"vertex-degree closed forms: M1 failures={m1_fail} (max err {m1_err:.2e}), "
          f"F failures={f3_fail} (max err {f3_err:.2e})", flush=True)
    with open("results/general_identity.json", "w") as fh:
        json.dump({"graphs_checked": len(recs), "per_index": rows,
                   "M1_formula_failures": m1_fail, "M1_max_err": m1_err,
                   "F_formula_failures": f3_fail, "F_max_err": f3_err}, fh, indent=1)
    print(f"[{time.time()-t0:.1f}s] wrote results/general_identity.csv/json", flush=True)


if __name__ == "__main__":
    main()
