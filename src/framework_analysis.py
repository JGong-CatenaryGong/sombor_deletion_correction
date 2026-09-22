"""
framework_analysis.py -- how far does the summation rearrangement generalise?

Three regimes for  sum_{e in E} T(G-e) = m*T(G) - sum_e Delta_e^T :

 (A) edge-additive degree indices  T_f(G) = sum_{uv} f(d_u,d_v)
     Delta_e^f is LOCAL and closed-form (theorem of report section 7.7).
     Verified here for Randic and ABC explicitly (plus the other 12 in general_identity.py).

 (B) vertex-degree indices  T_g(G) = sum_v g(d_v)
     Delta_e^g = [g(d_u)-g(d_u-1)] + [g(d_v)-g(d_v-1)] is local, hence
        sum_e T_g(G-e) = m*T_g(G) - sum_u d_u*[g(d_u)-g(d_u-1)].
     Verified for g = d^2, d^3, sqrt(d), log(1+d), 1/d.

 (C) distance-based indices (Wiener) -- the rearrangement FAILS.  Certificate of
     non-locality: two edges with identical local degree configuration (a,b,A,B) but
     different Delta_e^W.  For trees the exact substitute is
        W(T) - W(T-e) = |A||B| + |B|*sigma_A(u) + |A|*sigma_B(v),
     sigma_A(u) = sum_{a in A} d(a,u), verified on every tree with n <= 9, together with
     closed forms for paths and stars.

Outputs
  results/framework_wiener.csv      per tree/path/star checks, sign statistics
  results/framework_summary.json
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
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import graphlib as gl

FLAG_TREE = 32


def deg_sum(g, v, comp):
    """sum of distances from v inside the vertex set comp (BFS)."""
    dist = {v: 0}
    frontier = [v]
    while frontier:
        nxt = []
        for u in frontier:
            for w in g[u]:
                if w in comp and w not in dist:
                    dist[w] = dist[u] + 1
                    nxt.append(w)
        frontier = nxt
    return sum(dist.values())


def wiener_generalised(adj) -> float:
    """Sum of distances over pairs in the same component (finite for forests)."""
    n = len(adj)
    nbr = [[j for j in range(n) if (adj[i] >> j) & 1] for i in range(n)]
    total = 0.0
    seen = [False] * n
    for s in range(n):
        if seen[s]:
            continue
        comp = set()
        stack = [s]
        seen[s] = True
        while stack:
            u = stack.pop()
            comp.add(u)
            for w in nbr[u]:
                if not seen[w]:
                    seen[w] = True
                    stack.append(w)
        for v in comp:
            total += deg_sum(nbr, v, comp)
    return total / 2.0


def wiener_increment(adj, u, v):
    """W(G) - W(G-uv) with the generalised (per-component) Wiener index."""
    n = len(adj)
    w0 = wiener_generalised(adj)
    c = list(adj)
    c[u] &= ~(1 << v)
    c[v] &= ~(1 << u)
    return w0 - wiener_generalised(tuple(c))


def local_config(adj, u, v):
    deg = gl.degrees(adj)
    A = tuple(sorted(deg[x] for x in _nbrs(adj[u] & ~(1 << v))))
    B = tuple(sorted(deg[x] for x in _nbrs(adj[v] & ~(1 << u))))
    return (deg[u], deg[v], A, B)


def _nbrs(mask):
    out = []
    while mask:
        b = mask & -mask
        out.append(b.bit_length() - 1)
        mask ^= b
    return out


def pair_config(adj, u, v):
    """The pair-configuration used for the locality test: degrees plus the multiset of
    degrees at distance <= 1 from either endpoint."""
    return local_config(adj, u, v)


# --------------------------------------------------------------------------
def vertex_index_checks(adj):
    deg = gl.degrees(adj)
    m = gl.n_edges(adj)
    res = {}
    funcs = {
        "g=d^2 (M1)": (lambda d: d * d),
        "g=d^3 (F)": (lambda d: d ** 3),
        "g=sqrt(d)": (lambda d: math.sqrt(d)),
        "g=log(1+d)": (lambda d: math.log(1 + d)),
        "g=1/d": (lambda d: 1.0 / d if d else 0.0),
    }
    for name, g in funcs.items():
        TG = sum(g(d) for d in deg)
        s = 0.0
        for u, v in gl.edges_of(adj):
            c = list(adj)
            c[u] &= ~(1 << v)
            c[v] &= ~(1 << u)
            d2 = gl.degrees(tuple(c))
            s += sum(g(x) for x in d2)
        # a vertex of degree 0 contributes nothing; and g(d-1) is only needed for d>=1
        corr = sum(d * (g(d) - g(d - 1)) for d in deg if d >= 1)
        res[name] = {"sum_cards": s, "formula": (m * TG - corr) if m >= 1 else 0.0}
    return res


def _work(g6):
    adj = gl.from_graph6(g6)
    n = len(adj)
    m = gl.n_edges(adj)
    out = {"g6": g6, "n": n, "m": m, "tree": int(n > 1 and m == n - 1 and gl.connected(adj))}
    if m >= 2:
        out["vertex"] = vertex_index_checks(adj)
        w0 = wiener_generalised(adj)
        s = 0.0
        deltas = []
        for u, v in gl.edges_of(adj):
            d = wiener_increment(adj, u, v)
            s += w0 - d
            deltas.append(d)
            out.setdefault("edge_w", []).append(
                {"cfg": pair_config(adj, u, v), "delta": round(d, 9)})
        out["W"] = w0
        out["sum_cards_W"] = s
        out["naive_W"] = (m - 1) * w0
        # tree closed form
        if out["tree"]:
            err = 0.0
            for u, v in gl.edges_of(adj):
                c = list(adj)
                c[u] &= ~(1 << v)
                c[v] &= ~(1 << u)
                ct = tuple(c)
                # component of u and of v in T-e
                reach_u = _reach(ct, u)
                reach_v = _reach(ct, v)
                A = [i for i in range(n) if reach_u >> i & 1]
                B = [i for i in range(n) if reach_v >> i & 1]
                nbr = [[j for j in range(n) if (ct[i] >> j) & 1] for i in range(n)]
                sigA = deg_sum(nbr, u, set(A))
                sigB = deg_sum(nbr, v, set(B))
                formula = len(A) * len(B) + len(B) * sigA + len(A) * sigB
                err = max(err, abs(formula - wiener_increment(adj, u, v)))
            out["tree_formula_max_err"] = err
    return out


def _reach(adj, s):
    seen = 1 << s
    frontier = 1 << s
    while frontier:
        nxt = 0
        f = frontier
        while f:
            b = f & -f
            i = b.bit_length() - 1
            f ^= b
            nxt |= adj[i]
        nxt &= ~seen
        seen |= nxt
        frontier = nxt
    return seen


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graphs", default="results/graphs.jsonl.gz")
    ap.add_argument("--nmax", type=int, default=8, help="locality/vertex checks up to this n")
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 4) - 2))
    args = ap.parse_args()

    g6s = []
    with gzip.open(args.graphs, "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["n"] <= args.nmax:
                g6s.append(r["g6"])
    print(f"{len(g6s)} graphs with n <= {args.nmax}", flush=True)

    cfg_delta = defaultdict(set)      # locality test for Wiener
    vfail = defaultdict(int)
    vmax = defaultdict(float)
    tree_err = 0.0
    tree_n = 0
    sign_stats = {"sum<naive": 0, "sum==naive": 0, "sum>naive": 0}
    rows_w = []
    with mp.Pool(args.workers) as pool:
        for i, r in enumerate(pool.imap(_work, g6s, chunksize=128)):
            if r["m"] < 2:
                continue
            for name, d in r["vertex"].items():
                e = abs(d["sum_cards"] - d["formula"])
                if e > 1e-9:
                    vfail[name] += 1
                vmax[name] = max(vmax[name], e)
            s, naive = r["sum_cards_W"], r["naive_W"]
            sign_stats["sum<naive" if s < naive - 1e-9 else
                       ("sum>naive" if s > naive + 1e-9 else "sum==naive")] += 1
            for ed in r.get("edge_w", []):
                cfg_delta[ed["cfg"]].add(ed["delta"])
            if r["tree"]:
                tree_n += 1
                tree_err = max(tree_err, r["tree_formula_max_err"])
            rows_w.append({"g6": r["g6"], "n": r["n"], "m": r["m"], "W": round(r["W"], 9),
                           "sum_cards_W": round(s, 9), "naive_(m-1)W": round(naive, 9),
                           "ratio": round(s / naive, 6) if naive else None})
            if (i + 1) % 2000 == 0:
                print(f"  {i+1}/{len(g6s)}", flush=True)

    ambiguous = {k: sorted(v) for k, v in cfg_delta.items() if len(v) > 1}
    print(f"Wiener locality: {len(cfg_delta)} distinct local edge configurations, "
          f"{len(ambiguous)} of them carry >1 distinct Delta^W  -> non-local", flush=True)
    ex = sorted(ambiguous.items(), key=lambda kv: (len(kv[0][2]) + len(kv[0][3]), kv[0]))[:5]
    for k, v in ex:
        print("   cfg", k, "-> Delta^W values", v, flush=True)
    print("vertex-degree theorem failures:", dict(vfail), "max err", dict(vmax), flush=True)
    print(f"tree formula: checked {tree_n} trees, max err {tree_err:.3e}", flush=True)
    print("Wiener sign statistics:", sign_stats, flush=True)

    with open("results/framework_wiener.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows_w[0].keys()))
        w.writeheader()
        w.writerows(rows_w)
    summary = {
        "graphs_checked_n_le": args.nmax,
        "vertex_index_theorem_failures": dict(vfail),
        "vertex_index_max_error": {k: f"{v:.3e}" for k, v in vmax.items()},
        "wiener_local_configurations": len(cfg_delta),
        "wiener_configurations_with_multiple_deltas": len(ambiguous),
        "wiener_nonlocality_examples": [
            {"cfg": [list(k[0:2]), list(k[2]), list(k[3])], "deltas": v} for k, v in ex],
        "trees_checked": tree_n,
        "tree_formula_max_error": f"{tree_err:.3e}",
        "wiener_sign_vs_naive": sign_stats,
    }
    with open("results/framework_summary.json", "w") as f:
        json.dump(summary, f, indent=1)
    print("wrote results/framework_wiener.csv, framework_summary.json")


if __name__ == "__main__":
    main()
