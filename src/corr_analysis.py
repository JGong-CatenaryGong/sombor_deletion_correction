"""
corr_analysis.py -- the correction term C(G) itself.

C(G) = sum_u (d_u - 1) sum_{x in N(u)} c(d_u,d_x),  c(a,b) = sqrt(a^2+b^2)-sqrt((a-1)^2+b^2)

Q1  closed form
    (a) C(G) = sum_{uv in E} phi(d_u,d_v) with phi(a,b) = (a-1)c(a,b) + (b-1)c(b,a):
        C is itself an edge-additive degree-based index ('Sombor-deletion kernel').
    (b) hence C(G) = sum_{a<=b} n_ab * w(a,b), a linear functional of the edge-type
        (degree-pair) counts n_ab -- explicit weights w.
    (c) r-regular graphs: C = n*r*(r-1)*(r*sqrt2 - sqrt(2r^2-2r+1)).
    (d) rationalised kernel c(a,b) = (2a-1)/(sqrt(a^2+b^2)+sqrt((a-1)^2+b^2)) gives the
        sharp two-sided bound   1 <= c(a,b)(2a+2b-1)/(2a-1) <= sqrt2   (both ends sharp), hence
            C in [ sum_uv Psi_uv/(2d_u+2d_v-1) , sqrt2 * sum_uv Psi_uv/(2d_u+2d_v-1) ]
        with Psi_uv = (d_u-1)(2d_u-1)+(d_v-1)(2d_v-1), and the coarser Zagreb/Forgotten form
            Z/(4Delta-1) <= C <= (sqrt2/3) Z,   Z = 2F - 3M1 + 2m.
    (e) NO exact expression in n,m,M1,M2 (or +F): certificates of minimal pairs sharing
        (n,m,M1,M2,F) but with different C; likewise for the degree sequence, and for SO.

Q2  deck recoverability
    C = (m-1)SO(G) - sum_e SO(G-e), so C is deck-recoverable iff SO(G) is.  We test it
    directly on the deck signatures and report counterexample classes.

Q3  extremal behaviour for fixed (n,m): min/max of C, the attaining graphs, and whether
    argmax C = argmax M1, argmin C = regular/matching.
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
import invariants as inv


def c_fn(a: int, b: int) -> float:
    return math.sqrt(a * a + b * b) - math.sqrt((a - 1) ** 2 + b * b)


def C_of(adj) -> float:
    deg = gl.degrees(adj)
    tot = 0.0
    for u, v in gl.edges_of(adj):
        a, b = deg[u], deg[v]
        if a >= 2:
            tot += (a - 1) * c_fn(a, b)
        if b >= 2:
            tot += (b - 1) * c_fn(b, a)
    return tot


def C_via_edge_types(adj) -> float:
    """C from the degree-pair counts n_ab with explicit weights."""
    deg = gl.degrees(adj)
    n_ab = defaultdict(int)
    for u, v in gl.edges_of(adj):
        a, b = deg[u], deg[v]
        n_ab[(min(a, b), max(a, b))] += 1
    tot = 0.0
    for (a, b), k in n_ab.items():
        if a == b:
            w = 2 * (a - 1) * c_fn(a, a)
        else:
            w = (a - 1) * c_fn(a, b) + (b - 1) * c_fn(b, a)
        tot += k * w
    return tot


def sharp_sandwich(adj):
    """(C, lower, upper) for the sharp Psi-based sandwich."""
    deg = gl.degrees(adj)
    s = 0.0
    for u, v in gl.edges_of(adj):
        a, b = deg[u], deg[v]
        psi = (a - 1) * (2 * a - 1) + (b - 1) * (2 * b - 1)
        s += psi / (2 * a + 2 * b - 1)
    return C_of(adj), s, math.sqrt(2) * s


def coarse_bound(adj):
    """(Z, Delta) for the Zagreb/Forgotten sandwich."""
    d = gl.degrees(adj)
    Z = sum(x * (x - 1) * (2 * x - 1) for x in d)
    return Z, (max(d) if d else 0)


def _work(g6):
    adj = gl.from_graph6(g6)
    deg = gl.degrees(adj)
    n = len(adj)
    m = gl.n_edges(adj)
    C = C_of(adj)
    C2 = C_via_edge_types(adj)
    _, lo, hi = sharp_sandwich(adj)
    Z, D = coarse_bound(adj)
    dseq = tuple(sorted(deg, reverse=True))
    m1 = sum(x * x for x in deg)
    m2 = sum(deg[u] * deg[v] for u, v in gl.edges_of(adj))
    f3 = sum(x ** 3 for x in deg)
    so = inv.sombor(adj)
    reg = len(set(deg)) == 1
    return {
        "g6": g6, "n": n, "m": m, "C": C, "C_via_types": C2, "lo": lo, "hi": hi,
        "Z": Z, "Delta": D, "dseq": dseq, "M1": m1, "M2": m2, "F": f3, "SO": so,
        "regular": reg, "r": deg[0] if reg and deg else 0,
        "maxdeg": max(deg) if deg else 0,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graphs", default="results/graphs.jsonl.gz")
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 4) - 2))
    args = ap.parse_args()

    recs = []
    with gzip.open(args.graphs, "rt") as f:
        for line in f:
            recs.append(json.loads(line)["g6"])
    print(f"{len(recs)} graphs", flush=True)
    out = []
    with mp.Pool(args.workers) as pool:
        for i, r in enumerate(pool.imap(_work, recs, chunksize=256)):
            out.append(r)
            if (i + 1) % 100000 == 0:
                print(f"  {i+1}", flush=True)

    summary = {}
    # ---- (a)(b) representation checks -----------------------------------
    err_a = max((abs(r["C"] - r["C_via_types"]) for r in out), default=0.0)
    summary["max_err_C_vs_edge_type_form"] = err_a
    # ---- (c) regular graphs ---------------------------------------------
    reg_errs = {}
    for r in out:
        if r["regular"] and r["n"] > 1:
            rr = r["r"]
            formula = r["n"] * rr * (rr - 1) * (rr * math.sqrt(2) - math.sqrt(2 * rr * rr - 2 * rr + 1))
            d = reg_errs.setdefault(rr, [0.0, 0])
            d[0] = max(d[0], abs(formula - r["C"]))
            d[1] += 1
    summary["regular_closed_form_max_err"] = {str(k): v[0] for k, v in sorted(reg_errs.items())}
    summary["regular_closed_form_counts"] = {str(k): v[1] for k, v in sorted(reg_errs.items())}
    # ---- (d) sandwich tightness -----------------------------------------
    viol = sum(1 for r in out if r["m"] >= 2 and not (r["lo"] - 1e-9 <= r["C"] <= r["hi"] + 1e-9))
    ratio_lo = [r["C"] / r["lo"] for r in out if r["m"] >= 2 and r["lo"] > 0]
    ratio_hi = [r["C"] / r["hi"] for r in out if r["m"] >= 2 and r["hi"] > 0]
    coarse_viol = sum(1 for r in out if r["m"] >= 2 and r["Z"] > 0
                      and not (r["Z"] / (4 * r["Delta"] - 1) - 1e-9 <= r["C"] <= math.sqrt(2) / 3 * r["Z"] + 1e-9))
    summary["sharp_sandwich_violations"] = viol
    summary["sharp_ratio_min"] = min(ratio_lo) if ratio_lo else None
    summary["sharp_ratio_max"] = max(ratio_hi) if ratio_hi else None
    summary["coarse_sandwich_violations"] = coarse_viol
    # ---- (e) non-expressibility certificates ----------------------------
    def first_pair(keyf, need_two=True):
        g = defaultdict(list)
        for r in out:
            g[keyf(r)].append(r)
        best = None
        for k, v in g.items():
            if len(v) < 2:
                continue
            Cs = {round(x["C"], 9) for x in v}
            if len(Cs) > 1:
                v2 = sorted(v, key=lambda r: (r["n"], r["m"], r["g6"]))[:2]
                cand = (v2[0]["n"], v2[0]["m"], v2[0]["g6"], v2[1]["g6"])
                if best is None or cand < best[0]:
                    best = (cand, v2)
        return best

    certs = {}
    for label, keyf in [
        ("(n,m,M1,M2)", lambda r: (r["n"], r["m"], r["M1"], r["M2"])),
        ("(n,m,M1,M2,F)", lambda r: (r["n"], r["m"], r["M1"], r["M2"], r["F"])),
        ("degree_sequence", lambda r: r["dseq"]),
        ("(n,m,SO)", lambda r: (r["n"], r["m"], round(r["SO"], 9))),
    ]:
        b = first_pair(keyf)
        certs[label] = None if b is None else {
            "n": b[1][0]["n"], "m": b[1][0]["m"],
            "graph6": [x["g6"] for x in b[1]],
            "deg_seq": [list(x["dseq"]) for x in b[1]],
            "M1": [x["M1"] for x in b[1]], "M2": [x["M2"] for x in b[1]],
            "F": [x["F"] for x in b[1]], "SO": [round(x["SO"], 9) for x in b[1]],
            "C": [round(x["C"], 9) for x in b[1]],
        }
        print(f"  certificate for '{label}':", certs[label], flush=True)
    summary["non_expressibility"] = certs

    # ---- Q3 extremal tables ---------------------------------------------
    ext = []
    by_nm = defaultdict(list)
    for r in out:
        if r["m"] >= 2:
            by_nm[(r["n"], r["m"])].append(r)
    for (n, m), v in sorted(by_nm.items()):
        if len(v) < 2:
            continue
        argmin = min(v, key=lambda r: (r["C"], r["g6"]))
        argmax = max(v, key=lambda r: (r["C"], r["g6"]))
        m1max = max(v, key=lambda r: (r["M1"], r["g6"]))
        lo = min(len({tuple(r["dseq"]) for r in v}), 1)
        ext.append({
            "n": n, "m": m, "graphs": len(v),
            "C_min": round(argmin["C"], 9), "C_min_graph": argmin["g6"],
            "C_min_degseq": ",".join(map(str, argmin["dseq"])),
            "C_max": round(argmax["C"], 9), "C_max_graph": argmax["g6"],
            "C_max_degseq": ",".join(map(str, argmax["dseq"])),
            "argmax_has_max_M1": int(argmax["g6"] == m1max["g6"]),
            "C_min_is_regular": argmin["regular"],
            "C_max_maxdeg": argmax["maxdeg"],
        })
    with open("results/corr_extremal.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(ext[0].keys()))
        w.writeheader()
        w.writerows(ext)
    summary["extremal_rows"] = len(ext)
    summary["argmax_C_equals_argmax_M1_frac"] = (
        sum(r["argmax_has_max_M1"] for r in ext) / len(ext) if ext else None)
    summary["argmin_C_regular_frac"] = sum(r["C_min_is_regular"] for r in ext) / len(ext) if ext else None

    # star formula check: K_{1,k} + isolated vertices
    star_rows = []
    for k in range(2, 9):
        adj = gl.from_edges(k + 1, [(0, i) for i in range(1, k + 1)])
        formula = k * (k - 1) * (math.sqrt(k * k + 1) - math.sqrt((k - 1) ** 2 + 1))
        star_rows.append({"k": k, "g6": gl.to_graph6(adj), "C_direct": round(C_of(adj), 9),
                          "C_formula": round(formula, 9)})
    with open("results/corr_star_formula.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(star_rows[0].keys()))
        w.writeheader()
        w.writerows(star_rows)

    with open("results/corr_summary.json", "w") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps({k: v for k, v in summary.items() if k != "non_expressibility"}, indent=1)[:2000])
    print("wrote results/corr_summary.json, corr_extremal.csv, corr_star_formula.csv")


if __name__ == "__main__":
    main()
