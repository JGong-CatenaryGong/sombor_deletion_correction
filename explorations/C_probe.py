"""
C-probe: feasibility evidence for research directions C1/C2/C3 (探索方向.md C-class).

Single pass over the frozen dataset (all n<=9 graphs) computing, per graph:
  C        = sum_{uv in E} phi(d_u,d_v),  phi(a,b) = (a-1)c(a,b) + (b-1)c(b,a)
  psiSum   = sum_{uv in E} Psi(a,b)/(2a+2b-1)
  exact C  = integer coordinate vector of C over the multiquadratic basis
             {sqrt(s) : s squarefree}  (A3 normal-form machinery)

C1 evidence: per-(n,m) argmin of C over CONNECTED graphs; quasi-regular fraction;
             arrangement effect (spread of C within a fixed degree sequence);
             majorization rank of the argmin degree sequence.
C2 evidence: ratio C/psiSum in [1, sqrt2]: distribution + extremal graph families;
             explicit (n,m) bound (sqrt2/3)(k z(n-1) + z(r)) tightness per (n,m)
             (max C / bound) + argmax degree sequences.
C3 evidence: exact-coordinate collision scan (graphs with EQUAL exact C vectors but
             DISTINCT edge-type multisets, excluding the C=0 matching family);
             minimum true gap between distinct exact C values (float + exact pair);
             integer relation lattice of the weights {phi(x,y)} for Delta<=4 and
             Delta<=8 (rank, kernel dimension, smallest relations via sympy).

Read-only on the frozen baseline. Output: explorations/results/C_probe.json
"""
import os
import sys
import gzip
import json
import math
from fractions import Fraction
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "src"))
import graphlib as gl

FLAG_CONNECTED = 1
SQRT2 = math.sqrt(2.0)


# ---------- exact integer-coordinate machinery (A3 style) ----------

def sqrt_vec(N: int) -> dict:
    """sqrt(N) as {squarefree s : coefficient g} with N = g^2 * s."""
    g = 1
    d = 2
    n = N
    while d * d <= n:
        while n % (d * d) == 0:
            n //= d * d
            g *= d
        d += 1
    return {n: g}


def vadd(a: dict, b: dict) -> dict:
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + v
        if out[k] == 0:
            del out[k]
    return out


def vmul(a: dict, k: int) -> dict:
    return {s: g * k for s, g in a.items()} if k else {}


PHI_VEC = {}
PHI_FLOAT = {}
PSI_DEN = {}


def phi_vec(x: int, y: int) -> dict:
    """Exact vector of phi(x,y) = (x-1)c(x,y) + (y-1)c(y,x)
       = (x+y-2)sqrt(x^2+y^2) - (x-1)sqrt((x-1)^2+y^2) - (y-1)sqrt((y-1)^2+x^2)."""
    key = (x, y)
    if key not in PHI_VEC:
        v = vmul(sqrt_vec(x * x + y * y), x + y - 2)
        v = vadd(v, vmul(sqrt_vec((x - 1) ** 2 + y * y), -(x - 1)))
        v = vadd(v, vmul(sqrt_vec((y - 1) ** 2 + x * x), -(y - 1)))
        PHI_VEC[key] = v
    return PHI_VEC[key]


def phi_float(x: int, y: int) -> float:
    key = (x, y)
    if key not in PHI_FLOAT:
        c1 = math.sqrt(x * x + y * y) - math.sqrt((x - 1) ** 2 + y * y)
        c2 = math.sqrt(x * x + y * y) - math.sqrt((y - 1) ** 2 + x * x)
        PHI_FLOAT[key] = (x - 1) * c1 + (y - 1) * c2
    return PHI_FLOAT[key]


def vec_value(v: dict) -> float:
    return sum(g * math.sqrt(s) for s, g in v.items())


def cell_key(a: int, b: int):
    return (a, b) if a <= b else (b, a)


# ---------- C2 bound helpers ----------

def z(d: int) -> int:
    return d * (d - 1) * (2 * d - 1)


def explicit_bound(n: int, m: int) -> float:
    """(sqrt2/3)(k z(n-1) + z(r)) with 2m = k(n-1) + r, 0 <= r < n-1 (report 8.3)."""
    if n < 2:
        return float("inf")
    k, r = divmod(2 * m, n - 1)
    return (SQRT2 / 3.0) * (k * z(n - 1) + z(r))


def degseq_bound(deg) -> float:
    """sum_u d(d-1) c(d,1)."""
    s = 0.0
    for d in deg:
        if d >= 1:
            s += d * (d - 1) * (math.sqrt(d * d + 1) - math.sqrt((d - 1) ** 2 + 1))
    return s


def main():
    # per-(n,m) aggregates
    cmin = {}          # (n,m) -> (C, g6, ds) over connected
    cmax_conn = {}     # (n,m) -> (C, g6, ds) over connected graphs
    by_degseq = defaultdict(list)   # (n, ds-tuple) -> list of (C, g6) connected
    exact_groups = defaultdict(list)  # exact C vec key -> list of (g6, etype key)
    distinct_vals = {}               # exact vec key -> (float C, g6 sample)
    ratio_lo_ext = []                # (C/psiSum, g6, ds) for m>=1, psiSum>0
    ratio_hi_ext = []
    n_graphs = 0
    n_conn = 0

    with gzip.open(os.path.join(ROOT, "results", "graphs.jsonl.gz"), "rt") as f:
        for line in f:
            r = json.loads(line)
            n, m = r["n"], r["m"]
            ds = [int(t) for t in r["ds"].split(",")]
            n_graphs += 1
            conn = bool(r["fl"] & FLAG_CONNECTED)
            if conn:
                n_conn += 1
            adj = gl.from_graph6(r["g6"])
            deg = gl.degrees(adj)

            # edge-type multiset (unordered cells), C float, psiSum, exact vec
            et = Counter()
            C = 0.0
            psi = 0.0
            cvec = {}
            for u, v in gl.edges_of(adj):
                a, b = deg[u], deg[v]
                k = cell_key(a, b)
                et[k] += 1
                C += phi_float(a, b)
                psi += ((a - 1) * (2 * a - 1) + (b - 1) * (2 * b - 1)) / (2 * a + 2 * b - 1)
                cvec = vadd(cvec, phi_vec(*k))
            etkey = tuple(sorted(et.items()))
            etstrip = tuple(sorted((k, v) for k, v in et.items() if k != (1, 1)))
            vkey = tuple(sorted(cvec.items()))
            exact_groups[vkey].append((r["g6"], etkey, etstrip, n, m))
            if vkey not in distinct_vals:
                distinct_vals[vkey] = (C, r["g6"])

            # C1/C2 aggregates
            if conn and m >= 1:
                key = (n, m)
                if key not in cmin or C < cmin[key][0]:
                    cmin[key] = (C, r["g6"], r["ds"])
                if key not in cmax_conn or C > cmax_conn[key][0]:
                    cmax_conn[key] = (C, r["g6"], r["ds"])
                dskey = (n, tuple(sorted(ds)))
                by_degseq[dskey].append((C, r["g6"]))
                if psi > 0:
                    lo = C / psi
                    ratio_lo_ext.append((lo, r["g6"], r["ds"], n, m))
                    ratio_hi_ext.append((C / (SQRT2 * psi), r["g6"], r["ds"], n, m))
            if m >= 1:
                pass  # (all-graph maxima removed: explicit bound analysed on connected graphs)

    # ---------- C1 summary ----------
    qr_hits = 0
    leaf_argmin = 0
    argmin_rows = []
    for (n, m), (C, g6, dss) in sorted(cmin.items()):
        ds = [int(t) for t in dss.split(",")]
        qr = (max(ds) - min(ds)) <= 1
        qr_hits += int(qr)
        leaf = 1 in ds
        leaf_argmin += int(leaf)
        argmin_rows.append({"n": n, "m": m, "C": C, "ds": dss,
                            "quasi_regular": qr, "has_leaf": leaf})
    # arrangement effect: spread of C within identical (n, ds) connected classes
    spread_stats = {"classes_ge2": 0, "classes_with_spread": 0, "max_spread": 0.0,
                    "examples": [],
                    "qr_classes_ge2": 0, "qr_classes_with_spread": 0,
                    "qr_max_spread": 0.0, "qr_examples": []}
    for (n, dst), lst in by_degseq.items():
        is_qr = (max(dst) - min(dst)) <= 1
        if len(lst) >= 2:
            spread_stats["classes_ge2"] += 1
            cs = [c for c, _ in lst]
            sp = max(cs) - min(cs)
            if is_qr:
                spread_stats["qr_classes_ge2"] += 1
                if sp > 1e-9:
                    spread_stats["qr_classes_with_spread"] += 1
                    spread_stats["qr_max_spread"] = max(spread_stats["qr_max_spread"], sp)
                    if len(spread_stats["qr_examples"]) < 5:
                        spread_stats["qr_examples"].append(
                            {"n": n, "ds": list(dst), "spread": sp,
                             "C_min_graph": min(lst)[1], "C_max_graph": max(lst)[1]})
            if sp > 1e-9:
                spread_stats["classes_with_spread"] += 1
                if sp > spread_stats["max_spread"]:
                    spread_stats["max_spread"] = sp
                if len(spread_stats["examples"]) < 6:
                    lo_g = min(lst)[1]
                    hi_g = max(lst)[1]
                    spread_stats["examples"].append(
                        {"n": n, "ds": list(dst), "spread": sp,
                         "C_min_graph": lo_g, "C_max_graph": hi_g})

    # ---------- C2 summary ----------
    ratio_lo_ext.sort(key=lambda t: t[0])
    ratio_hi_ext.sort(key=lambda t: -t[0])
    los = [t[0] for t in ratio_lo_ext]
    his = [t[0] for t in ratio_hi_ext]
    c2 = {
        "n_measured": len(los),
        "C_over_psiSum": {"min": los[0], "mean": sum(los) / len(los), "max": los[-1],
                          "sqrt2": SQRT2},
        "C_over_sqrt2psi": {"min": his[-1], "mean": sum(his) / len(his), "max": his[0]},
        "lower_tight_examples": [{"ratio": t[0], "g6": t[1], "ds": t[2]} for t in ratio_lo_ext[:6]],
        "upper_tight_examples": [{"ratio": t[0], "g6": t[1], "ds": t[2]} for t in ratio_hi_ext[:6]],
    }
    # explicit (n,m) bound tightness -- over CONNECTED graphs only (m >= n-1);
    # for m < n-1 no connected graph exists and max C = 0 is trivial (matchings)
    bnd_rows = []
    for (n, m), (C, g6, dss) in sorted(cmax_conn.items()):
        b = explicit_bound(n, m)
        if b > 0 and math.isfinite(b) and C > 0:
            bnd_rows.append({"n": n, "m": m, "maxC": C, "bound": b, "ratio": C / b,
                             "argmax_ds": dss, "g6": g6})
    bnd_rows.sort(key=lambda r: r["ratio"])
    c2["explicit_bound"] = {
        "min_ratio": bnd_rows[0]["ratio"] if bnd_rows else None,
        "min_ratio_row": bnd_rows[0] if bnd_rows else None,
        "max_ratio": bnd_rows[-1]["ratio"] if bnd_rows else None,
        "worst_5": bnd_rows[:5],
        "best_3": bnd_rows[-3:],
    }

    # ---------- C3 summary ----------
    # raw collisions: same exact C vector, different FULL edge-type multisets.
    # refined: compare multisets after stripping the (1,1) cell -- adding/removing
    # matching components (phi(1,1)=0) trivially preserves C, so the meaningful
    # question is injectivity modulo the matching direction.
    collisions_raw = []
    collisions = []
    zero_vec_key = tuple()
    for vkey, lst in exact_groups.items():
        if vkey == zero_vec_key:
            continue
        ets_full = set(e for _, e, _, _, _ in lst)
        ets_strip = set(e for _, _, e, _, _ in lst)
        if len(ets_full) >= 2:
            collisions_raw.append({"n_graphs": len(lst), "n_distinct_etypes": len(ets_full)})
        if len(ets_strip) >= 2:
            nms = set((nn, mm) for _, _, _, nn, mm in lst)
            collisions.append({"vec": [list(t) for t in vkey],
                               "C_approx": vec_value(dict(vkey)),
                               "n_graphs": len(lst), "n_distinct_stripped_etypes": len(ets_strip),
                               "n_distinct_nm": len(nms),
                               "same_nm_pairs": len(nms) < len(lst),
                               "examples": [(g, [list(t) for t in e]) for g, _, e, _, _ in lst[:4]]})
    vals = sorted(distinct_vals.items(), key=lambda kv: kv[1][0])
    min_gap = None
    min_gap_pair = None
    for i in range(1, len(vals)):
        (k1, (gv1, g1)), (k2, (gv2, g2)) = vals[i - 1], vals[i]
        gap = gv2 - gv1
        if gap > 1e-12 and (min_gap is None or gap < min_gap):
            min_gap = gap
            min_gap_pair = {"C_lo": gv1, "C_hi": gv2, "gap": gap,
                            "g6_lo": g1, "g6_hi": g2,
                            "vec_lo": [list(t) for t in k1], "vec_hi": [list(t) for t in k2]}

    # relation lattices for phi weights
    def relation_lattice(D: int):
        cells = [(x, y) for x in range(1, D + 1) for y in range(x, D + 1) if (x, y) != (1, 1)]
        basis = sorted({s for (x, y) in cells for s in phi_vec(x, y)})
        idx = {s: i for i, s in enumerate(basis)}
        M = []
        for (x, y) in cells:
            row = [0] * len(basis)
            for s, g in phi_vec(x, y).items():
                row[idx[s]] = g
            M.append(row)
        import sympy
        Ms = sympy.Matrix(M)
        rank = Ms.rank()
        ns = Ms.T.nullspace()   # relations among ROWS (cells): v^T M = 0
        dim = len(ns)
        int_basis = []
        for v in ns:
            den = 1
            for e in v:
                den = den * e.q // math.gcd(den, e.q) if hasattr(e, "q") else den
            iv = [int(e * den) for e in v]
            g = 0
            for t in iv:
                g = math.gcd(g, t)
            int_basis.append([t // g for t in iv] if g else iv)
        # smallest relations: search small combinations of the basis
        small = []
        if 1 <= dim <= 4:
            rng = range(-3, 4)
            import itertools
            for coeffs in itertools.product(rng, repeat=dim):
                if all(c == 0 for c in coeffs):
                    continue
                rel = [sum(coeffs[j] * int_basis[j][i] for j in range(dim))
                       for i in range(len(cells))]
                nz = sum(1 for t in rel if t)
                mx = max(abs(t) for t in rel)
                if mx <= 6 and nz <= 6:
                    small.append({"coeffs_on_kernel_basis": list(coeffs),
                                  "relation": {f"phi{cells[i]}": rel[i] for i in range(len(cells)) if rel[i]}})
            small.sort(key=lambda d: (max(abs(v) for v in d["relation"].values()),
                                      len(d["relation"])))
            small = small[:8]
        return {"D": D, "n_cells": len(cells), "basis_squarefree": basis,
                "rank": rank, "kernel_dim": dim,
                "integer_kernel_basis": int_basis, "small_relations": small}

    lat4 = relation_lattice(4)
    lat8 = relation_lattice(8)

    c3 = {
        "n_graphs_scanned": n_graphs,
        "n_distinct_exact_C_values": len(distinct_vals),
        "n_raw_collision_classes_nonzero": len(collisions_raw),
        "n_refined_collision_classes": len(collisions),
        "refined_collisions": collisions[:10],
        "zero_vector_graphs": len(exact_groups.get(zero_vec_key, [])),
        "min_true_gap": min_gap,
        "min_gap_pair": min_gap_pair,
        "relation_lattice_D4": lat4,
        "relation_lattice_D8": {k: v for k, v in lat8.items() if k != "small_relations"},
        "relation_lattice_D8_small_relations": lat8["small_relations"][:4],
    }

    out = {
        "script": "explorations/C_probe.py",
        "dataset": {"n_graphs": n_graphs, "n_connected": n_conn},
        "C1": {
            "n_nm_classes": len(cmin),
            "argmin_quasi_regular_fraction": qr_hits / len(cmin) if cmin else None,
            "argmin_has_leaf_fraction": leaf_argmin / len(cmin) if cmin else None,
            "arrangement_spread": spread_stats,
            "argmin_table_sample": argmin_rows[:40],
        },
        "C2": c2,
        "C3": c3,
    }
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    with open(os.path.join(HERE, "results", "C_probe.json"), "w") as f:
        json.dump(out, f, indent=1, default=str)

    # console summary
    print(f"graphs {n_graphs} (connected {n_conn})")
    print(f"C1: argmin quasi-regular {qr_hits}/{len(cmin)}  has-leaf {leaf_argmin}/{len(cmin)}")
    print(f"C1: arrangement classes>=2: {spread_stats['classes_ge2']}, "
          f"with spread: {spread_stats['classes_with_spread']}, max {spread_stats['max_spread']:.4f}")
    print(f"C2: C/psiSum in [{los[0]:.6f}, {los[-1]:.6f}]  mean {sum(los)/len(los):.4f}; "
          f"C/(sqrt2 psi) max {his[0]:.6f}")
    print(f"C2: explicit bound min ratio {c2['explicit_bound']['min_ratio']:.4f} at "
          f"{c2['explicit_bound']['min_ratio_row']}")
    print(f"C3: distinct exact C values {len(distinct_vals)}; raw collisions {len(collisions_raw)}; "
          f"refined (mod matching) {len(collisions)}; zero-vec graphs {len(exact_groups.get(zero_vec_key, []))}")
    print(f"C3: min true gap {min_gap}")
    print(f"C3 lattice D4: cells {lat4['n_cells']}, rank {lat4['rank']}, kernel dim {lat4['kernel_dim']}")
    print(f"   smallest relations: {json.dumps(lat4['small_relations'][:3], default=str)}")
    print(f"C3 lattice D8: cells {lat8['n_cells']}, rank {lat8['rank']}, kernel dim {lat8['kernel_dim']}")
    print("wrote explorations/results/C_probe.json")


if __name__ == "__main__":
    main()
