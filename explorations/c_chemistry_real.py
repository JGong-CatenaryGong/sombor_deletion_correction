"""
C-chemistry: real-molecule analysis on the 18 octane isomers (item 4).

Part 1 (fully self-contained, no external data): build the 18 carbon skeletons,
compute C, Sombor (SO), ABC, M1 (first Zagreb), Wiener, Randic, and the edge-type
multiset; test whether each invariant separates all 18 isomers (discriminating
power on a real molecular set) and record which pairs collide.

Part 2 (needs experimental data): correlation with the standard tabulated
boiling points of the octane isomers, including the incremental value of C over
SO / M1 (OLS R^2 + leave-one-out cross-validation, and Spearman).

Part 3 (paper Sec. 7, second paragraph): the five-property sweep over the same
18 isomers --- boiling point, entropy, acentric factor and the two vaporisation
enthalpies --- C against the seven single indices, the SO + C joint regression
against the best single index (compared at equal parameter count, adjusted
R^2), and the structural tie-pair check.

NOTE on the experimental data: the boiling points below are the standard
literature values for the 18 octane isomers (as tabulated in the
topological-index literature and in CRC/NIST handbooks), cross-checked against
the NIST WebBook.  The five-property columns are from the moleculardescriptors.eu
QSPR benchmark (Needham, Wei & Seybold) as recorded in the octane data file.
"""
import os
import sys
import json
import math
import gzip
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, ".pylibs"))
sys.path.insert(0, os.path.join(ROOT, "src"))
import graphlib as gl

# ---------- molecules: carbon skeletons as edge lists (trees on 8 vertices) ----------
def path(n, start=0):
    return [(start + i, start + i + 1) for i in range(n - 1)]


def build(name, edges, n=8):
    return (name, gl.from_edges(n, [tuple(sorted(e)) for e in edges]))


MOLECULES = []
MOLECULES.append(build("n-octane", path(8)))
MOLECULES.append(build("2-methylheptane", path(7) + [(1, 7)]))
MOLECULES.append(build("3-methylheptane", path(7) + [(2, 7)]))
MOLECULES.append(build("4-methylheptane", path(7) + [(3, 7)]))
MOLECULES.append(build("3-ethylhexane", path(6) + [(2, 6), (6, 7)]))
MOLECULES.append(build("2,2-dimethylhexane", path(6) + [(1, 6), (1, 7)]))
MOLECULES.append(build("2,3-dimethylhexane", path(6) + [(1, 6), (2, 7)]))
MOLECULES.append(build("2,4-dimethylhexane", path(6) + [(1, 6), (3, 7)]))
MOLECULES.append(build("2,5-dimethylhexane", path(6) + [(1, 6), (4, 7)]))
MOLECULES.append(build("3,3-dimethylhexane", path(6) + [(2, 6), (2, 7)]))
MOLECULES.append(build("3,4-dimethylhexane", path(6) + [(2, 6), (3, 7)]))
MOLECULES.append(build("2,2,3-trimethylpentane", path(5) + [(1, 5), (1, 6), (2, 7)]))
MOLECULES.append(build("2,2,4-trimethylpentane", path(5) + [(1, 5), (1, 6), (3, 7)]))
MOLECULES.append(build("2,3,3-trimethylpentane", path(5) + [(1, 5), (2, 6), (2, 7)]))
MOLECULES.append(build("2,3,4-trimethylpentane", path(5) + [(1, 5), (2, 6), (3, 7)]))
MOLECULES.append(build("3-ethyl-2-methylpentane", path(5) + [(1, 5), (2, 6), (6, 7)]))
MOLECULES.append(build("3-ethyl-3-methylpentane", path(5) + [(2, 5), (2, 6), (6, 7)]))
MOLECULES.append(build("2,2,3,3-tetramethylbutane", path(4) + [(1, 4), (1, 5), (2, 6), (2, 7)]))

BP = {  # standard tabulated boiling points, deg C (cross-checked against NIST WebBook)
    "n-octane": 125.7, "2-methylheptane": 117.6, "3-methylheptane": 118.9,
    "4-methylheptane": 117.7, "3-ethylhexane": 118.5, "2,2-dimethylhexane": 106.8,
    "2,3-dimethylhexane": 115.6, "2,4-dimethylhexane": 109.4, "2,5-dimethylhexane": 109.1,
    "3,3-dimethylhexane": 111.9, "3,4-dimethylhexane": 117.7,
    "2,2,3-trimethylpentane": 109.8, "2,2,4-trimethylpentane": 99.2,
    "2,3,3-trimethylpentane": 114.8, "2,3,4-trimethylpentane": 113.5,
    "3-ethyl-2-methylpentane": 115.6, "3-ethyl-3-methylpentane": 118.3,
    "2,2,3,3-tetramethylbutane": 106.5,
}

FIVE_PROPERTIES = {  # QSPR benchmark columns (moleculardescriptors.eu), 18 isomers
    "S": {  # entropy
        "n-octane": 111.67, "2-methylheptane": 109.84, "3-methylheptane": 111.26,
        "4-methylheptane": 109.32, "3-ethylhexane": 109.43, "2,2-dimethylhexane": 103.42,
        "2,3-dimethylhexane": 108.02, "2,4-dimethylhexane": 106.98,
        "2,5-dimethylhexane": 105.72, "3,3-dimethylhexane": 104.74,
        "3,4-dimethylhexane": 106.59, "2,2,3-trimethylpentane": 101.31,
        "2,2,4-trimethylpentane": 104.09, "2,3,3-trimethylpentane": 102.06,
        "2,3,4-trimethylpentane": 102.39, "3-ethyl-2-methylpentane": 106.06,
        "3-ethyl-3-methylpentane": 101.48, "2,2,3,3-tetramethylbutane": 93.06,
    },
    "AcenFac": {  # acentric factor
        "n-octane": 0.3979, "2-methylheptane": 0.3779, "3-methylheptane": 0.371,
        "4-methylheptane": 0.3715, "3-ethylhexane": 0.3625, "2,2-dimethylhexane": 0.3394,
        "2,3-dimethylhexane": 0.3482, "2,4-dimethylhexane": 0.3442,
        "2,5-dimethylhexane": 0.3568, "3,3-dimethylhexane": 0.3226,
        "3,4-dimethylhexane": 0.3403, "2,2,3-trimethylpentane": 0.3008,
        "2,2,4-trimethylpentane": 0.3054, "2,3,3-trimethylpentane": 0.2932,
        "2,3,4-trimethylpentane": 0.3174, "3-ethyl-2-methylpentane": 0.3324,
        "3-ethyl-3-methylpentane": 0.3069, "2,2,3,3-tetramethylbutane": 0.2553,
    },
    "HVAP": {  # enthalpy of vaporisation
        "n-octane": 73.19, "2-methylheptane": 70.3, "3-methylheptane": 71.3,
        "4-methylheptane": 70.91, "3-ethylhexane": 71.7, "2,2-dimethylhexane": 67.7,
        "2,3-dimethylhexane": 70.2, "2,4-dimethylhexane": 68.5,
        "2,5-dimethylhexane": 68.6, "3,3-dimethylhexane": 68.5,
        "3,4-dimethylhexane": 70.2, "2,2,3-trimethylpentane": 67.3,
        "2,2,4-trimethylpentane": 64.87, "2,3,3-trimethylpentane": 68.1,
        "2,3,4-trimethylpentane": 68.37, "3-ethyl-2-methylpentane": 69.7,
        "3-ethyl-3-methylpentane": 69.3, "2,2,3,3-tetramethylbutane": 66.2,
    },
    "DHVAP": {  # standard enthalpy of vaporisation
        "n-octane": 9.915, "2-methylheptane": 9.484, "3-methylheptane": 9.521,
        "4-methylheptane": 9.483, "3-ethylhexane": 9.476, "2,2-dimethylhexane": 8.915,
        "2,3-dimethylhexane": 9.272, "2,4-dimethylhexane": 9.029,
        "2,5-dimethylhexane": 9.051, "3,3-dimethylhexane": 8.973,
        "3,4-dimethylhexane": 9.316, "2,2,3-trimethylpentane": 8.826,
        "2,2,4-trimethylpentane": 8.402, "2,3,3-trimethylpentane": 8.897,
        "2,3,4-trimethylpentane": 9.014, "3-ethyl-2-methylpentane": 9.209,
        "3-ethyl-3-methylpentane": 9.081, "2,2,3,3-tetramethylbutane": 8.41,
    },
}


def c(a, b):
    return math.sqrt(a * a + b * b) - math.sqrt((a - 1) ** 2 + b * b)


def indices(adj):
    d = gl.degrees(adj)
    edges = gl.edges_of(adj)
    C = sum((d[u] - 1) * c(d[u], d[v]) + (d[v] - 1) * c(d[v], d[u]) for u, v in edges)
    SO = sum(math.sqrt(d[u] ** 2 + d[v] ** 2) for u, v in edges)
    ABC = sum(math.sqrt((d[u] + d[v] - 2) / (d[u] * d[v])) for u, v in edges)
    M1 = sum(x * x for x in d)
    M2 = sum(d[u] * d[v] for u, v in edges)
    R = sum(1.0 / math.sqrt(d[u] * d[v]) for u, v in edges)
    dm = gl.distance_matrix(adj)
    W = sum(dm[i][j] for i in range(len(adj)) for j in range(i + 1, len(adj)))
    et = tuple(sorted((min(d[u], d[v]), max(d[u], d[v])) for u, v in edges))
    return {"C": C, "SO": SO, "ABC": ABC, "M1": M1, "M2": M2, "Randic": R,
            "Wiener": W, "ds": tuple(sorted(d, reverse=True)), "et": et}


def spearman(x, y):
    def rank(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r = [0.0] * len(v)
        i = 0
        while i < len(order):
            j = i
            while j + 1 < len(order) and v[order[j + 1]] == v[order[i]]:
                j += 1
            avg = (i + j) / 2.0 + 1
            for k in range(i, j + 1):
                r[order[k]] = avg
            i = j + 1
        return r
    rx, ry = rank(x), rank(y)
    n = len(x)
    mx, my = sum(rx) / n, sum(ry) / n
    num = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    den = math.sqrt(sum((a - mx) ** 2 for a in rx) * sum((b - my) ** 2 for b in ry))
    return num / den if den else float("nan")


def pearson(x, y):
    n = len(x)
    mx, my = sum(x) / n, sum(y) / n
    num = sum((a - mx) * (b - my) for a, b in zip(x, y))
    den = math.sqrt(sum((a - mx) ** 2 for a in x) * sum((b - my) ** 2 for b in y))
    return num / den if den else float("nan")


def ols_r2(X, y):
    """X: list of feature vectors (with intercept added), y: targets. Returns R^2."""
    n, p = len(X), len(X[0])
    # normal equations via Gaussian elimination on (X^T X) b = X^T y
    A = [[sum(X[k][i] * X[k][j] for k in range(n)) for j in range(p)] + [sum(X[k][i] * y[k] for k in range(n))] for i in range(p)]
    for c_ in range(p):
        piv = max(range(c_, p), key=lambda r: abs(A[r][c_]))
        A[c_], A[piv] = A[piv], A[c_]
        if abs(A[c_][c_]) < 1e-12:
            return float("nan")
        for r in range(p):
            if r != c_ and A[r][c_] != 0:
                f = A[r][c_] / A[c_][c_]
                A[r] = [a - f * b for a, b in zip(A[r], A[c_])]
    b = [A[i][p] / A[i][i] for i in range(p)]
    yhat = [sum(b[i] * X[k][i] for i in range(p)) for k in range(n)]
    ybar = sum(y) / n
    ss_res = sum((y[k] - yhat[k]) ** 2 for k in range(n))
    ss_tot = sum((y[k] - ybar) ** 2 for k in range(n))
    return 1 - ss_res / ss_tot


def main():
    rows = []
    for name, adj in MOLECULES:
        d = gl.degrees(adj)
        assert len(adj) == 8 and gl.connected(adj) and max(d) <= 4 and gl.is_forest(adj), name
        idx = indices(adj)
        idx["name"] = name
        idx["BPs"] = BP[name]
        rows.append(idx)

    # Part 1: discriminating power on the real molecular set
    names = [r["name"] for r in rows]
    keys = ["C", "SO", "ABC", "M1", "M2", "Randic", "Wiener"]
    disc = {}
    for k in keys:
        groups = Counter(round(r[k], 9) for r in rows)
        coll = {v: c_ for v, c_ in groups.items() if c_ > 1}
        disc[k] = {"n_distinct": len(groups), "n_colliding_values": len(coll),
                   "examples": [names[i] for i in range(len(names))
                                if round(rows[i][k], 9) in coll][:6]}
    # edge-type multiset discrimination
    et_groups = Counter(r["et"] for r in rows)
    disc["edge_types"] = {"n_distinct": len(et_groups),
                          "n_colliding_values": sum(1 for v in et_groups.values() if v > 1)}
    ds_groups = Counter(r["ds"] for r in rows)
    disc["degree_sequence"] = {"n_distinct": len(ds_groups),
                               "n_colliding_values": sum(1 for v in ds_groups.values() if v > 1)}

    # Part 2: correlations with boiling point + incremental value of C
    bp = [r["BPs"] for r in rows]
    corr = {k: {"pearson": pearson([r[k] for r in rows], bp),
                "spearman": spearman([r[k] for r in rows], bp)} for k in keys}
    X_so = [[1.0, r["SO"]] for r in rows]
    X_m1 = [[1.0, r["M1"]] for r in rows]
    X_c = [[1.0, r["C"]] for r in rows]
    X_both = [[1.0, r["SO"], r["C"]] for r in rows]
    X_all = [[1.0, r["SO"], r["M1"], r["C"], r["Wiener"]] for r in rows]
    r2 = {"SO": ols_r2(X_so, bp), "M1": ols_r2(X_m1, bp), "C": ols_r2(X_c, bp),
          "SO+C": ols_r2(X_both, bp), "SO+M1+C+W": ols_r2(X_all, bp)}
    # leave-one-out for SO and SO+C
    def loo(X):
        errs = []
        for i in range(len(bp)):
            Xt = [X[k] for k in range(len(bp)) if k != i]
            yt = [bp[k] for k in range(len(bp)) if k != i]
            p = len(X[0])
            A = [[sum(Xt[k][a] * Xt[k][b] for k in range(len(Xt))) for b in range(p)]
                 + [sum(Xt[k][a] * yt[k] for k in range(len(Xt)))] for a in range(p)]
            for c_ in range(p):
                piv = max(range(c_, p), key=lambda rr: abs(A[rr][c_]))
                A[c_], A[piv] = A[piv], A[c_]
                if abs(A[c_][c_]) < 1e-12:
                    return float("nan")
                for rr in range(p):
                    if rr != c_ and A[rr][c_] != 0:
                        f = A[rr][c_] / A[c_][c_]
                        A[rr] = [a - f * b for a, b in zip(A[rr], A[c_])]
            b = [A[j][p] / A[j][j] for j in range(p)]
            pred = sum(b[j] * X[i][j] for j in range(p))
            errs.append((bp[i] - pred) ** 2)
        return math.sqrt(sum(errs) / len(errs))
    loo_rmse = {"SO": loo(X_so), "C": loo(X_c), "SO+C": loo(X_both)}

    # Part 3: five-property sweep (paper Sec. 7, second paragraph)
    five_props = {"BP": bp}
    for pname, vals in FIVE_PROPERTIES.items():
        five_props[pname] = [vals[r["name"]] for r in rows]

    def adj_r2(r2_, p):
        return 1 - (1 - r2_) * (len(rows) - 1) / (len(rows) - p)

    five = {}
    for pname, y in five_props.items():
        rs = {k: pearson([r[k] for r in rows], y) for k in keys}
        best = max(keys, key=lambda k: abs(rs[k]))
        r2_joint = ols_r2([[1.0, r["SO"], r["C"]] for r in rows], y)
        r2_best = ols_r2([[1.0, r[best]] for r in rows], y)
        five[pname] = {
            "abs_r": {k: abs(v) for k, v in rs.items()},
            "best_single": best, "best_abs_r": abs(rs[best]),
            "r2_SO_plus_C": r2_joint, "r2_best_single": r2_best,
            "adj_r2_SO_plus_C": adj_r2(r2_joint, 3),
            "adj_r2_best_single": adj_r2(r2_best, 2),
            "improves_at_equal_parameter_count": adj_r2(r2_joint, 3) > adj_r2(r2_best, 2),
        }
    by_name = {r["name"]: r for r in rows}
    ties = {}
    for a, b in [("3-methylheptane", "4-methylheptane"),
                 ("3,4-dimethylhexane", "3-ethyl-2-methylpentane")]:
        ties[f"{a} / {b}"] = {
            "same_C": abs(by_name[a]["C"] - by_name[b]["C"]) < 1e-9,
            "same_SO": abs(by_name[a]["SO"] - by_name[b]["SO"]) < 1e-9,
            "same_edge_type_multiset": by_name[a]["et"] == by_name[b]["et"],
        }

    out = {
        "script": "explorations/c_chemistry_real.py",
        "n_molecules": len(rows),
        "part1_discriminating_power": disc,
        "part2_boiling_point": {"pearson": {k: v["pearson"] for k, v in corr.items()},
                                "spearman": {k: v["spearman"] for k, v in corr.items()},
                                "ols_r2": r2, "loo_rmse": loo_rmse,
                                "data_status": "standard tabulated values (moleculardescriptors.eu QSPR benchmark; boiling points cross-checked against NIST WebBook)"},
        "part3_five_properties": {"properties": list(five_props.keys()),
                                  "values": FIVE_PROPERTIES,
                                  "stats": five,
                                  "tie_pairs_structural": ties},
        "table": [{"name": r["name"], "ds": list(r["ds"]), "C": r["C"], "SO": r["SO"],
                   "ABC": r["ABC"], "M1": r["M1"], "Wiener": r["Wiener"], "BP": r["BPs"]}
                  for r in rows],
    }
    with open(os.path.join(HERE, "results", "c_chemistry_real.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("discriminating power (18 octane isomers):")
    for k, v in disc.items():
        print(f"  {k:14s} distinct {v['n_distinct']:2d}/18  colliding values {v['n_colliding_values']}")
    print("\nboiling-point correlation:")
    for k in keys:
        print(f"  {k:8s} pearson {corr[k]['pearson']:+.3f}  spearman {corr[k]['spearman']:+.3f}")
    print("\nOLS R^2:", {k: round(v, 4) for k, v in r2.items()})
    print("LOO RMSE:", {k: round(v, 3) for k, v in loo_rmse.items()})
    print("\nfive-property sweep (paper Sec. 7):")
    for pname, s in five.items():
        print(f"  {pname:8s} |r(C)|={s['abs_r']['C']:.3f}  best={s['best_single']} "
              f"({s['best_abs_r']:.3f})  SO+C vs best adj-R2: "
              f"{s['adj_r2_SO_plus_C']:.4f} vs {s['adj_r2_best_single']:.4f}  "
              f"improves={s['improves_at_equal_parameter_count']}")
    print("tie pairs:", ties)
    print("wrote explorations/results/c_chemistry_real.json")


if __name__ == "__main__":
    main()
