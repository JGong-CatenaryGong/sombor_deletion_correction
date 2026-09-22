"""
star_theorem.py -- verification of the star-maximisation theorem for C(G).

THEOREM.  For every simple graph G with m >= 2 edges,
      C(G) <= m(m-1) c(m,1) = C(K_{1,m}),
with equality iff G is the star K_{1,m} plus isolated vertices.
(Consequently, for every pair (n,m) with m <= n-1 the maximum of C over graphs
with n vertices and m edges is attained exactly by K_{1,m} + (n-1-m) K_1.)

PROOF (three lines, all ingredients elementary).
 (L1) Monotonicity of c.  c(a,b) = (2a-1)/D, D = sqrt(a^2+b^2)+sqrt((a-1)^2+b^2);
      D >= 2a-1 with equality iff b = 0, and D is increasing in b, so c is strictly
      increasing in a (for b >= 1) and strictly decreasing in b (for a >= 1).
      Hence for every edge uv of a graph with m edges (d_u, d_v <= m):
          c(d_u,d_v) <= c(d_u,1) <= c(m,1),   c(d_v,d_u) <= c(v,1) <= c(m,1).
 (L2) For every edge uv:  d_u + d_v <= m + 1.
      Indeed v is adjacent to u and all other edges at v are among the m - d_u edges
      not incident with u, so d_v <= 1 + (m - d_u).
 (L3) M1 = sum_u d_u^2 = sum_{uv in E} (d_u + d_v) <= m(m+1).
      (each of the m edges contributes at most m+1, by L2)
 Then, with phi(a,b) = (a-1)c(a,b) + (b-1)c(b,a),
      C(G) = sum_{uv} phi(d_u,d_v) <= sum_{uv} (d_u+d_v-2) c(m,1)
           = (M1 - 2m) c(m,1) <= m(m-1) c(m,1) = C(K_{1,m}).       []
 Equality: M1 = m(m+1) forces d_u+d_v = m+1 for *every* edge (L3 is a sum of m terms
 each <= m+1); equality in (L1) for an edge forces (d_u,d_v) in {(1,1),(m,1),(1,m)}
 (strict monotonicity).  For m >= 2 the type (1,1) is excluded (2 = m+1), so every
 edge is incident with a vertex of degree m and its other endpoint has degree 1:
 the component of such a vertex is exactly K_{1,m} and uses all m edges.

Related bounds proved and tested here (note: c is *decreasing* in its second
argument, so sum_{x in N(u)} c(d_u,d_x) <= d_u c(d_u,1) -- the degree-sequence
expression below is an UPPER bound, not a lower one as one might first guess):
      C(G) <= sum_u d_u(d_u-1) c(d_u,1) <= (M1(G)-2m) c(m,1) <= m(m-1)c(m,1),
      C(G) >= sum_u d_u(d_u-1) c(d_u,Delta),
      C(G) >= Z(G)/(4 Delta - 1) >= (M1-m)(M1-2m) / (m (4 Delta - 1)),
      sum_{uv} Psi_uv/(2d_u+2d_v-1) <= C(G) <= sqrt2 * sum_{uv} Psi_uv/(2d_u+2d_v-1).

Outputs
  results/star_theorem.json     theorem checks, equality cases, bound tightness
  results/star_bounds.csv       per-graph comparison of all upper/lower bounds
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

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import graphlib as gl


def c(a: int, b: int) -> float:
    return math.sqrt(a * a + b * b) - math.sqrt((a - 1) ** 2 + b * b)


def analyse(g6: str) -> dict:
    adj = gl.from_graph6(g6)
    d = gl.degrees(adj)
    n = len(adj)
    edges = gl.edges_of(adj)
    m = len(edges)
    if m < 1:
        return {"g6": g6, "n": n, "m": 0}
    C = 0.0
    psi_sum = 0.0
    for u, v in edges:
        a, b = d[u], d[v]
        if a >= 2:
            C += (a - 1) * c(a, b)
        if b >= 2:
            C += (b - 1) * c(b, a)
        psi = (a - 1) * (2 * a - 1) + (b - 1) * (2 * b - 1)
        psi_sum += psi / (2 * a + 2 * b - 1)
    M1 = sum(x * x for x in d)
    F = sum(x ** 3 for x in d)
    Z = 2 * F - 3 * M1 + 2 * m
    D = max(d)
    cm1 = c(m, 1)
    L = sum(x * (x - 1) * c(x, 1) for x in d)          # UPPER bound (c decreasing in b)
    LB_Delta = sum(x * (x - 1) * c(x, D) for x in d)   # lower: c(d_u,d_x) >= c(d_u,Delta)
    LB_m = sum(x * (x - 1) * c(x, m) for x in d)       # lower: c(d_u,d_x) >= c(d_u,m)
    return {
        "g6": g6, "n": n, "m": m, "C": C, "M1": M1, "Z": Z, "Delta": D,
        "U_star": m * (m - 1) * cm1 if m >= 2 else 0.0,
        "U_M1": (M1 - 2 * m) * cm1,
        "U_Z": math.sqrt(2) / 3 * Z,
        "U_psi": math.sqrt(2) * psi_sum,
        "U_degseq": L,
        "LB_Delta": LB_Delta,
        "LB_m": LB_m,
        "L_Z": Z / (4 * D - 1) if D else 0.0,
        "L_psi": psi_sum,
        "deg_seq": tuple(sorted(d, reverse=True)),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graphs", default="results/graphs.jsonl.gz")
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 4) - 2))
    args = ap.parse_args()

    g6s = []
    with gzip.open(args.graphs, "rt") as f:
        for line in f:
            g6s.append(json.loads(line)["g6"])
    out = []
    with mp.Pool(args.workers) as pool:
        for i, r in enumerate(pool.imap(analyse, g6s, chunksize=256)):
            if r["m"] >= 1:
                out.append(r)
            if (i + 1) % 100000 == 0:
                print(f"  {i+1}/{len(g6s)}", flush=True)

    res = {"graphs_checked": len(out)}
    viol = lambda key: [r for r in out if r["m"] >= 2 and r["C"] > r[key] + 1e-10]
    res["violations_U_star"] = len(viol("U_star"))
    res["violations_U_M1"] = len(viol("U_M1"))
    res["violations_U_Z"] = len(viol("U_Z"))
    res["violations_U_psi"] = len(viol("U_psi"))
    res["violations_U_degseq"] = len([r for r in out if r["C"] > r["U_degseq"] + 1e-10])
    res["violations_LB_Delta"] = len([r for r in out if r["LB_Delta"] > r["C"] + 1e-10])
    res["violations_LB_m"] = len([r for r in out if r["LB_m"] > r["C"] + 1e-10])
    res["violations_L_Z"] = len([r for r in out if r["L_Z"] > r["C"] + 1e-10])
    res["violations_L_psi"] = len([r for r in out if r["L_psi"] > r["C"] + 1e-10])
    # equality cases of the theorem
    eq = [r for r in out if r["m"] >= 2 and abs(r["C"] - r["U_star"]) < 1e-10]
    def is_star(r):
        ds = r["deg_seq"]
        return ds[0] == r["m"] and sum(1 for x in ds if x == 1) == r["m"]
    res["theorem_equality_cases"] = len(eq)
    res["theorem_equality_all_stars"] = all(is_star(r) for r in eq)
    res["theorem_equality_examples"] = [r["g6"] for r in eq[:10]]
    # which intermediate bound is attained
    eqM1 = [r for r in out if r["m"] >= 2 and abs(r["C"] - r["U_M1"]) < 1e-10]
    res["U_M1_equality_cases"] = len(eqM1)
    res["U_M1_equality_all_stars"] = all(is_star(r) for r in eqM1)
    # tightness statistics
    def stats(key, upper=True):
        vs = [r["C"] / r[key] for r in out if r["m"] >= 2 and r[key] > 0]
        return {"min_ratio": min(vs), "mean_ratio": sum(vs) / len(vs), "max_ratio": max(vs)}
    for k in ["U_star", "U_M1", "U_Z", "U_psi"]:
        res[f"tightness_{k}"] = stats(k)
    for k in ["U_degseq", "L_Z", "L_psi", "LB_Delta", "LB_m"]:
        vs = [r[k] / r["C"] for r in out if r["m"] >= 2 and r["C"] > 0 and r[k] > 0]
        res[f"tightness_{k}"] = {"min_ratio": min(vs), "mean_ratio": sum(vs) / len(vs),
                                 "max_ratio": max(vs)}
    # which upper bound is the best (smallest) per graph
    best = {"U_M1": 0, "U_Z": 0, "U_psi": 0, "U_degseq": 0}
    for r in out:
        if r["m"] < 2:
            continue
        vals = {k: r[k] for k in best}
        best[min(vals, key=vals.get)] += 1
    res["best_upper_bound_counts"] = best
    res["m_range"] = [min(r["m"] for r in out), max(r["m"] for r in out)]
    with open("results/star_theorem.json", "w") as f:
        json.dump(res, f, indent=1)
    print(json.dumps(res, indent=1))
    with open("results/star_bounds.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["g6", "n", "m", "C", "M1", "Z", "Delta",
                                          "U_star", "U_M1", "U_Z", "U_psi", "U_degseq",
                                          "L_Z", "L_psi", "LB_Delta", "LB_m"])
        w.writeheader()
        for r in out:
            w.writerow({k: (f"{r[k]:.9f}" if isinstance(r[k], float) else r[k])
                        for k in w.fieldnames})
    print("wrote results/star_theorem.json, results/star_bounds.csv")


if __name__ == "__main__":
    main()
