"""
spectral_products.py -- two structural questions about C(G).

(1) HIDDEN RELATIONS with spectral / electrical invariants.
    C is a function of the edge degree-pair multiset only, while the Laplacian
    spectrum, the number of spanning trees tau, and the Kirchhoff (resistance)
    index are not.  We produce explicit certificates (minimal pairs with equal
    spectral/electrical invariant but different C) and quantify the *statistical*
    relation by rank correlations inside fixed (n,m) classes.

(2) BEHAVIOUR UNDER GRAPH PRODUCTS.
    For the Cartesian product  (u,v)~(u',v) or (u,v)~(u,v'),  d_(u,v) = d_u + d_v,
        C(G [] H) = sum_{uu' in E_G} sum_{v in V_H} phi(d_u+d_v, d_{u'}+d_v)
                  + sum_{vv' in E_H} sum_{u in V_G} phi(d_u+d_v, d_u+d_{v'}),
    for the tensor (direct) product d_(u,v) = d_u d_v and for the strong product
    d_(u,v) = (d_u+1)(d_v+1) - 1.  When both factors are regular these collapse to
    the r-regular closed form C = N R (R-1) c(R,R) (N vertices, R = product degree).
    All formulas are verified numerically.

Outputs
  results/spectral_certificates.json
  results/spectral_correlations.csv
  results/product_formulas.json
"""

from __future__ import annotations

import json
import math
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import numpy as np
from scipy.stats import rankdata

import graphlib as gl
import invariants as inv

RESULTS = "results"


def c(a: float, b: float) -> float:
    return math.sqrt(a * a + b * b) - math.sqrt((a - 1) ** 2 + b * b)


def phi(a: float, b: float) -> float:
    return (a - 1) * c(a, b) + (b - 1) * c(b, a)


def C_of(adj) -> float:
    d = gl.degrees(adj)
    return sum(phi(d[u], d[v]) for u, v in gl.edges_of(adj))


def regular_C_formula(N: int, R: int) -> float:
    """C of an R-regular graph on N vertices."""
    if R < 1:
        return 0.0
    return N * R * (R - 1) * (R * math.sqrt(2) - math.sqrt(2 * R * R - 2 * R + 1))


# --------------------------------------------------------------------------
# (1) spectral / electrical certificates
# --------------------------------------------------------------------------
def lap_spectrum(adj):
    return tuple(np.round(np.sort(inv.lap_spectrum(adj)), 9))


def kirchhoff_index(adj) -> float:
    """Kf(G) = n * sum_{i>=2} 1/mu_i  (resistance index)."""
    ev = np.sort(inv.lap_spectrum(adj))
    n = len(adj)
    s = sum(1.0 / x for x in ev if x > 1e-9)
    return n * s


def sum_resistance_pairs(adj) -> float:
    """Sum over pairs of effective resistances = Kirchhoff index (unweighted)."""
    return kirchhoff_index(adj)


def main():
    graphs = {}
    import gzip
    with gzip.open("results/graphs.jsonl.gz", "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["n"] <= 8 or (r["fl"] & 64):
                graphs[r["g6"]] = r

    # ---- certificates from recorded graph-level collisions -----------------
    certs = {}
    for src in ["graph:lap_spec", "graph:taus", "graph:adj_spec"]:
        try:
            ex = json.load(open("results/collision_examples.json"))
        except FileNotFoundError:
            break
        cand = sorted([e for e in ex if e["source"] == src], key=lambda e: (e["n"], e["m"]))
        # a certificate must actually separate C: the two graphs share the
        # invariant and C differs.  Trivial pairs (e.g. K1 vs K2, where both
        # C values are 0 and even the "shared" invariant differs) are skipped --
        # an earlier version recorded them as certificates.
        e = None
        for c_ in cand:
            adjs_ = [gl.from_graph6(g["g6"]) for g in c_["graphs"]]
            if abs(C_of(adjs_[0]) - C_of(adjs_[1])) > 1e-9:
                e = c_
                break
        if e is None:
            print(f"  [cert] {src}: no C-separating pair found, skipped", flush=True)
            continue
        pair = [g["g6"] for g in e["graphs"]]
        adjs = [gl.from_graph6(g) for g in pair]
        certs[src] = {
            "n": e["n"], "m": e["m"], "graphs": pair,
            "deg_seqs": [list(gl.degree_sequence(a)) for a in adjs],
            "C": [round(C_of(a), 9) for a in adjs],
            "differs": True,
            "shared_invariant": src.split(":")[1],
            "separates_C": True,
        }
    # ---- explicit Kirchhoff-index certificate ------------------------------
    # group graphs by (n, m) and Kirchhoff index, look for different C
    by = defaultdict(list)
    for g6, r in graphs.items():
        if r["m"] < 4 or r["m"] > 12:
            continue
        adj = gl.from_graph6(g6)
        by[(r["n"], r["m"], round(kirchhoff_index(adj), 6))].append((g6, adj))
    cert = None
    for k, v in sorted(by.items()):
        if len(v) > 1:
            Cs = {round(C_of(a), 9) for _, a in v}
            if len(Cs) > 1:
                v2 = sorted(v)[:2]
                cert = {"n": k[0], "m": k[1], "kirchhoff": k[2],
                        "graphs": [g for g, _ in v2],
                        "C": [round(C_of(a), 9) for _, a in v2],
                        "deg_seqs": [list(gl.degree_sequence(a)) for _, a in v2],
                        "differs": True, "shared_invariant": "kirchhoff",
                        "separates_C": True}
                break
    certs["graph:kirchhoff"] = cert
    with open("results/spectral_certificates.json", "w") as f:
        json.dump(certs, f, indent=1)
    print(json.dumps(certs, indent=1)[:1500], flush=True)

    # ---- statistical relations inside fixed (n,m) --------------------------
    rows = []
    groups = defaultdict(list)
    for g6, r in graphs.items():
        if r["m"] < 2:
            continue
        adj = gl.from_graph6(g6)
        d = gl.degrees(adj)
        rec = {
            "g6": g6, "n": r["n"], "m": r["m"], "C": C_of(adj),
            "taus": inv.n_spanning_trees(adj), "wiener": inv.distance_profile(adj)[1],
            "kirchhoff": kirchhoff_index(adj) if gl.connected(adj) else float("nan"),
            "deg_var": float(np.var(d)), "n_leaves": sum(1 for x in d if x == 1),
            "cyclomatic": r["m"] - r["n"] + gl.n_components(adj),
        }
        groups[(r["n"], r["m"])].append(rec)
    for (n, m), v in sorted(groups.items()):
        if len(v) < 8:
            continue
        def spearman(key):
            """Spearman rho with *average* ranks for ties (scipy.stats.rankdata).

            An earlier version ranked with argsort(argsort(.)), which breaks ties
            by position and is not the textbook Spearman coefficient; the
            difference matters for the discrete quantities (taus, n_leaves,
            n_branch), where ties are massive.
            """
            xs = np.array([r[key] for r in v], dtype=float)
            ys = np.array([r["C"] for r in v], dtype=float)
            ok = ~np.isnan(xs)
            if ok.sum() < 8:
                return None
            if np.all(xs[ok] == xs[ok][0]) or np.all(ys[ok] == ys[ok][0]):
                return None                       # correlation undefined (constant)
            rx = rankdata(xs[ok])
            ry = rankdata(ys[ok])
            return float(np.corrcoef(rx, ry)[0, 1])
        rows.append({
            "n": n, "m": m, "graphs": len(v),
            "spearman_C_vs_log_taus": spearman("taus"),
            "spearman_C_vs_wiener": spearman("wiener"),
            "spearman_C_vs_kirchhoff": spearman("kirchhoff"),
            "spearman_C_vs_degree_variance": spearman("deg_var"),
            "spearman_C_vs_n_leaves": spearman("n_leaves"),
        })
    with open("results/spectral_correlations.csv", "w", newline="") as f:
        import csv as _csv
        w = _csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    def mean_of(key):
        vs = [r[key] for r in rows if r[key] is not None]
        return sum(vs) / len(vs) if vs else None
    print("mean Spearman over (n,m) classes:",
          {k: round(mean_of(k), 3) for k in
           ["spearman_C_vs_log_taus", "spearman_C_vs_wiener", "spearman_C_vs_kirchhoff",
            "spearman_C_vs_degree_variance", "spearman_C_vs_n_leaves"]}, flush=True)

    # ---- (2) products ------------------------------------------------------
    def cartesian(A, B):
        nA, nB = len(A), len(B)
        n = nA * nB
        adj = [0] * n
        idx = lambda u, v: u * nB + v
        for u in range(nA):
            for up in range(nA):
                if (A[u] >> up) & 1:
                    for v in range(nB):
                        i, j = idx(u, v), idx(up, v)
                        adj[i] |= 1 << j
                        adj[j] |= 1 << i
        for v in range(nB):
            for vp in range(nB):
                if (B[v] >> vp) & 1:
                    for u in range(nA):
                        i, j = idx(u, v), idx(u, vp)
                        adj[i] |= 1 << j
                        adj[j] |= 1 << i
        return tuple(adj)

    def tensor(A, B):
        nA, nB = len(A), len(B)
        n = nA * nB
        adj = [0] * n
        idx = lambda u, v: u * nB + v
        for u in range(nA):
            for up in range(nA):
                if (A[u] >> up) & 1:
                    for v in range(nB):
                        for vp in range(nB):
                            if (B[v] >> vp) & 1:
                                i, j = idx(u, v), idx(up, vp)
                                adj[i] |= 1 << j
                                adj[j] |= 1 << i
        return tuple(adj)

    def strong(A, B):
        nA, nB = len(A), len(B)
        n = nA * nB
        adj = [0] * n
        idx = lambda u, v: u * nB + v
        for u in range(nA):
            for up in range(nA):
                for v in range(nB):
                    for vp in range(nB):
                        if u == up and v == vp:
                            continue
                        near_u = u == up or (A[u] >> up) & 1
                        near_v = v == vp or (B[v] >> vp) & 1
                        if near_u and near_v:
                            i, j = idx(u, v), idx(up, vp)
                            adj[i] |= 1 << j
                            adj[j] |= 1 << i
        return tuple(adj)

    def cartesian_formula(A, B):
        dA, dB = gl.degrees(A), gl.degrees(B)
        tot = 0.0
        for u, up in gl.edges_of(A):
            for v in range(len(B)):
                tot += phi(dA[u] + dB[v], dA[up] + dB[v])
        for v, vp in gl.edges_of(B):
            for u in range(len(A)):
                tot += phi(dA[u] + dB[v], dA[u] + dB[vp])
        return tot

    cases = []
    # (a) general Cartesian double-sum formula
    tests = [("P4", gl.from_edges(4, [(0, 1), (1, 2), (2, 3)]), "P3",
              gl.from_edges(3, [(0, 1), (1, 2)])),
             ("C4", gl.from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)]), "P3",
              gl.from_edges(3, [(0, 1), (1, 2)])),
             ("K13", gl.from_edges(4, [(0, 1), (0, 2), (0, 3)]), "K2",
              gl.from_edges(2, [(0, 1)]))]
    for na, A, nb, B in tests:
        P = cartesian(A, B)
        cases.append({"product": "cartesian", "factors": [na, nb],
                      "C_direct": round(C_of(P), 9),
                      "C_double_sum_formula": round(cartesian_formula(A, B), 9),
                      "match": abs(C_of(P) - cartesian_formula(A, B)) < 1e-9})
    # (b) regular factors -> closed form
    regs = {"K2": gl.from_edges(2, [(0, 1)]),
            "C3": gl.from_edges(3, [(0, 1), (1, 2), (2, 0)]),
            "C4": gl.from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
            "C5": gl.from_edges(5, [(i, (i + 1) % 5) for i in range(5)]),
            "K4": gl.from_edges(4, [(i, j) for i in range(4) for j in range(i + 1, 4)]),
            "K33": gl.from_edges(6, [(i, 3 + j) for i in range(3) for j in range(3)])}
    rdeg = {"K2": 1, "C3": 2, "C4": 2, "C5": 2, "K4": 3, "K33": 3}
    for na, nb in [("K2", "K2"), ("C4", "C4"), ("C3", "K2"), ("K4", "K2"), ("K33", "K2")]:
        A, B = regs[na], regs[nb]
        N = len(A) * len(B)
        R = rdeg[na] + rdeg[nb]
        P = cartesian(A, B)
        cases.append({"product": "cartesian", "factors": [na, nb], "N": N, "R": R,
                      "C_direct": round(C_of(P), 9),
                      "C_regular_formula": round(regular_C_formula(N, R), 9),
                      "match": abs(C_of(P) - regular_C_formula(N, R)) < 1e-9})
        Rt = rdeg[na] * rdeg[nb]
        T = tensor(A, B)
        cases.append({"product": "tensor", "factors": [na, nb], "N": N, "R": Rt,
                      "C_direct": round(C_of(T), 9),
                      "C_regular_formula": round(regular_C_formula(N, Rt), 9),
                      "match": abs(C_of(T) - regular_C_formula(N, Rt)) < 1e-9})
        Rs = (rdeg[na] + 1) * (rdeg[nb] + 1) - 1
        S = strong(A, B)
        cases.append({"product": "strong", "factors": [na, nb], "N": N, "R": Rs,
                      "C_direct": round(C_of(S), 9),
                      "C_regular_formula": round(regular_C_formula(N, Rs), 9),
                      "match": abs(C_of(S) - regular_C_formula(N, Rs)) < 1e-9})
    with open("results/product_formulas.json", "w") as f:
        json.dump(cases, f, indent=1)
    bad = [c for c in cases if not c["match"]]
    print(f"product formula checks: {len(cases)} cases, {len(bad)} failures", flush=True)
    for b in bad:
        print("   MISMATCH", b, flush=True)
    print("wrote results/spectral_certificates.json, spectral_correlations.csv, product_formulas.json")


if __name__ == "__main__":
    main()
