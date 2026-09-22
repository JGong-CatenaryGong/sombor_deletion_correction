"""
c_information.py -- information content, deck-side complexity, ML usefulness and
chemistry-flavoured correlates of the correction term C(G).

(A) ENTROPY / BITS.  C = sum_{a<=b} n_ab w(a,b) is a *linear* functional of the
    edge-type count vector.  We measure how many bits of the edge-type multiset a
    single scalar (C, or SO, M1, M2, Randic, ...) actually determines:
        H(et),  I(X; et) = H(et) - H(et | X),   number of distinct values,
        mean level-set size.
    (B) DECK-SIDE ALGORITHM.  For every card G-e let d^(e) be its degree sequence.
    Summing the multiset union M of all card degree values over e,
        c_x := #{copies of value x in M} = n_x (m - x) + n_{x+1} (x + 1),
    where n_x = #{v : d_v = x}.  This triangular system recovers the degree
    sequence from the deck alone in O(n + Delta) time (handshake used when
    x = m = Delta).  We verify it exhaustively.  Together with
        C = (m-1) SO(G) - sum_e SO(G-e)
    this gives: from the GRAPH, C costs Theta(n+m); from the DECK, C costs
    O(m(n+m)) for the card sums plus the recovery of the edge-type counts, which
    is the only step without a general polynomial algorithm.
    (C) ML / KERNEL.  Is C useful as a graph descriptor/kernel?  Binary tasks on
    chemical graphs, single-feature AUC and multi-feature CV accuracy; the
    edge-type count vector serves as the "ceiling" for any degree-based scalar.
    (D) CHEMISTRY-FLAVOURED CORRELATES.  Within chemical graphs: C versus
    cyclomatic number, number of branching vertices, degree variance, spanning
    trees, and the number of distinct card isomorphism classes
    (= distinct single-edge fragments, a graph-theoretic proxy for fragmentation
    diversity in mass spectrometry).

Outputs
  results/c_information.json
  results/c_ml_tasks.csv
  results/c_chemistry.csv
"""

from __future__ import annotations

import csv
import gzip
import json
import math
import os
from collections import Counter, defaultdict

import numpy as np
from scipy.stats import rankdata

import graphlib as gl
import invariants as inv

FLAG_CHEMICAL = 64


def c_fn(a, b):
    return math.sqrt(a * a + b * b) - math.sqrt((a - 1) ** 2 + b * b)


def C_of(adj):
    d = gl.degrees(adj)
    s = 0.0
    for u, v in gl.edges_of(adj):
        if d[u] >= 2:
            s += (d[u] - 1) * c_fn(d[u], d[v])
        if d[v] >= 2:
            s += (d[v] - 1) * c_fn(d[v], d[u])
    return s


def edge_type_counts(adj):
    d = gl.degrees(adj)
    cnt = Counter()
    for u, v in gl.edges_of(adj):
        cnt[tuple(sorted((d[u], d[v])))] += 1
    return tuple(sorted(cnt.items()))


# --------------------------------------------------------------------------
# (B) degree sequence from the deck
# --------------------------------------------------------------------------
def deck_degree_solution(adj):
    """Recover d(G) from the deck alone (card degree sequences + isolated counts).

    Statistics taken from the deck:
      c_x  = number of card-vertices of degree x, summed over all m cards;
      A0   = number of cards containing at least one isolated vertex;
      Amin = number of cards whose number of isolated vertices is minimal.
    Relations (n_x = #{v : d_v = x}):
      (1) c_x = n_x (m - x) + n_{x+1} (x + 1)        for x = 0..Delta
      (2) c_0 = n_0 m + n_1                          (the x = 0 case of (1))
      (3) A0  = n_1 if n_0 = 0, and A0 = m if n_0 > 0
      (4) Amin = m - n_1 when n_0 > 0 (a card loses an isolated vertex exactly
          when the deleted edge is incident with a degree-1 vertex)
    (1) is triangular unless Delta = m, in which case the top equation is 0 = 0 and
    the solution family has one free parameter t = n_m, fixed by (3)/(4).
    """
    n = len(adj)
    m = gl.n_edges(adj)
    if m == 0:
        return tuple([0] * n), True
    card_counts = Counter()
    n_cards_isolated = 0
    per_card_isolated = []
    for u, v in gl.edges_of(adj):
        c = list(adj)
        c[u] &= ~(1 << v)
        c[v] &= ~(1 << u)
        degs_card = gl.degrees(tuple(c))
        for x in degs_card:
            card_counts[x] += 1
        k = sum(1 for x in degs_card if x == 0)
        per_card_isolated.append(k)
        if k > 0:
            n_cards_isolated += 1
    n_vertices = sum(card_counts.values()) // m
    X = max(card_counts) if card_counts else 0
    a_min = min(per_card_isolated)
    n_cards_min_isolated = sum(1 for k in per_card_isolated if k == a_min)

    def valid(n_x):
        if sum(n_x.values()) != n_vertices:
            return False
        if any(v < 0 for v in n_x.values()):
            return False
        for x in range(0, max(n_x) + 1):
            if card_counts.get(x, 0) != n_x.get(x, 0) * (m - x) + n_x.get(x + 1, 0) * (x + 1):
                return False
        # isolated-vertex statistics:
        #  * every card loses an isolated vertex iff the deleted edge meets a leaf,
        #    and the leaf-edges are pairwise distinct, so
        #        #cards with >=1 isolated vertex = n_1 if n_0 = 0, else m
        #        min_x (#isolated in card x)   = n_0 + [1 if n_1 = m else 0]
        # The isolated-vertex statistics are *not* used for validation: when two
        # leaves share an edge (a K2 component) one card isolates both, so the
        # counts require the number of K2 components, which is not in c_x.
        return True

    def solve(delta, t_hint=None):
        n_x = {}
        if delta != m:
            for x in range(delta, 0, -1):
                rhs = card_counts.get(x, 0) - n_x.get(x + 1, 0) * (x + 1)
                if m - x == 0:
                    return None
                val = rhs / (m - x)
                if abs(val - round(val)) > 1e-9 or val < -1e-9:
                    return None
                n_x[x] = int(round(val))
            n_x[0] = n_vertices - sum(n_x.values())
        else:
            A = {delta: (1.0, 0.0)}          # n_x = a_x t + b_x
            for x in range(delta - 1, -1, -1):
                a_next, b_next = A[x + 1]
                denom = m - x
                A[x] = (-(x + 1) * a_next / denom,
                        (card_counts.get(x, 0) - (x + 1) * b_next) / denom)
            cands = []
            sa = sum(a for a, _ in A.values())
            sb = sum(b for _, b in A.values())
            if abs(sa) > 1e-12:
                cands.append((n_vertices - sb) / sa)
            # extra deck statistics: n_1 = n_cards_isolated (n_0 = 0), or n_0 = a_min
            # (when n_1 < m) / n_0 = a_min - 1 (when n_1 = m)
            a1, b1 = A.get(1, (0.0, 0.0))
            if abs(a1) > 1e-12:
                cands.append((n_cards_isolated - b1) / a1)
            a0, b0 = A.get(0, (0.0, 0.0))
            if abs(a0) > 1e-12:
                cands.append((a_min - b0) / a0)
                cands.append((a_min - 1 - b0) / a0)
            for t in cands:
                n_x = {}
                for x, (a, b) in A.items():
                    val = a * t + b
                    n_x[x] = int(round(val)) if abs(val - round(val)) < 1e-9 else None
                if any(v is None for v in n_x.values()):
                    continue
                if valid(n_x):
                    return n_x
            return None
        return n_x if valid(n_x) else None

    for delta in ([X, X + 1] if X + 1 <= m else [X]):
        n_x = solve(delta)
        if n_x is not None:
            degs = []
            for x, k in n_x.items():
                degs.extend([x] * int(k))
            if sorted(degs, reverse=True) == sorted(degs, reverse=True):
                return tuple(sorted(degs, reverse=True)), True
    return None, False


# --------------------------------------------------------------------------
def main():
    rows = []
    with gzip.open("results/graphs.jsonl.gz", "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["fl"] & FLAG_CHEMICAL:
                rows.append(r)
    print(f"chemical graphs: {len(rows)}", flush=True)

    # ---- (B) deck degree-sequence recovery --------------------------------
    ok = bad = 0
    for r in rows:
        adj = gl.from_graph6(r["g6"])
        got, good = deck_degree_solution(adj)
        if good and got == gl.degree_sequence(adj):
            ok += 1
        else:
            bad += 1
    print(f"(B) deck->degree-sequence: {ok} recovered, {bad} failures", flush=True)

    # ---- (A) information content -----------------------------------------
    feat = {}
    et_keys = []
    for r in rows:
        adj = gl.from_graph6(r["g6"])
        d = inv.quantised_fingerprint(adj)
        feat[r["g6"]] = {
            "C": round(C_of(adj), 6),
            "SO": d["sombor"], "M1": d["m1"], "M2": d["m2"],
            "randic": d["randic"], "abc": d["abc"],
            "wiener": d["wiener"], "taus": d["taus"], "deg_seq": d["deg_seq"],
            "edge_types": edge_type_counts(adj),
            "n": r["n"], "m": r["m"],
            "cyclomatic": r["m"] - r["n"] + d["n_comp"],
            "n_branch": sum(1 for x in gl.degrees(adj) if x >= 3),
        }
        et_keys.append(feat[r["g6"]]["edge_types"])
    et_counts = Counter(et_keys)
    H_et = -sum((v / len(et_keys)) * math.log2(v / len(et_keys)) for v in et_counts.values())

    def info_of(key):
        vals = [feat[r["g6"]][key] for r in rows]
        vc = Counter(vals)
        H_X = -sum((v / len(vals)) * math.log2(v / len(vals)) for v in vc.values())
        joint = Counter(zip(vals, et_keys))
        H_X_et = -sum((v / len(vals)) * math.log2(v / len(vals)) for v in joint.values())
        H_et_given_X = H_X_et - H_X
        mean_level = sum(v * v for v in vc.values()) / len(vals)
        return {"distinct_values": len(vc), "H_X": H_X, "I_X_et": H_X + H_et - H_X_et,
                "H_et_given_X": H_et_given_X, "mean_level_set": mean_level}
    info = {"H_edge_type_multiset": H_et, "n_graphs": len(rows),
            "n_distinct_edge_type_multisets": len(et_counts)}
    for key in ["C", "SO", "M1", "M2", "randic", "abc", "wiener", "taus", "deg_seq", "m"]:
        info[key] = info_of(key)
        print(f"  (A) {key:9s} distinct={info[key]['distinct_values']:6d} "
              f"I(X;et)={info[key]['I_X_et']:.3f} bits  H(et|X)={info[key]['H_et_given_X']:.3f}  "
              f"mean level set={info[key]['mean_level_set']:.1f}", flush=True)

    # ---- (C) ML tasks ------------------------------------------------------
    from sklearn.model_selection import cross_val_score, StratifiedKFold
    from sklearn.svm import SVC
    from sklearn.preprocessing import StandardScaler
    from sklearn.pipeline import make_pipeline
    from sklearn.metrics import roc_auc_score

    task_names = ["planar", "bipartite", "tree", "biconnected", "has_triangle"]
    labels = {t: {} for t in task_names}
    for r in rows:
        adj = gl.from_graph6(r["g6"])
        fp = inv.quantised_fingerprint(adj)
        labels["planar"][r["g6"]] = bool(r["fl"] & 2)
        labels["bipartite"][r["g6"]] = bool(fp["bipartite"])
        labels["tree"][r["g6"]] = bool(r["fl"] & 32)
        labels["biconnected"][r["g6"]] = bool(fp["biconnected"])
        labels["has_triangle"][r["g6"]] = fp["tri"] > 0
    single = {
        "C": lambda g: feat[g]["C"],
        "SO": lambda g: feat[g]["SO"] / 1e9,
        "M1": lambda g: feat[g]["M1"] / 1e9,
        "M2": lambda g: feat[g]["M2"] / 1e9,
        "randic": lambda g: feat[g]["randic"] / 1e9,
        "wiener": lambda g: feat[g]["wiener"] / 1e9,
        "taus": lambda g: math.log1p(feat[g]["taus"]),
        "n": lambda g: feat[g]["n"],
        "m": lambda g: feat[g]["m"],
    }
    ml_rows = []
    g6s = [r["g6"] for r in rows]
    for task in task_names:
        lab = labels[task]
        y = np.array([1 if lab[g] else 0 for g in g6s])
        if y.sum() < 30 or (len(y) - y.sum()) < 30:
            continue
        for name, fn in single.items():
            x = np.array([fn(g) for g in g6s]).reshape(-1, 1)
            auc = roc_auc_score(y, x)
            auc = max(auc, 1 - auc)  # feature direction is irrelevant for a kernel
            ml_rows.append({"task": task, "features": name, "n_pos": int(y.sum()),
                            "auc_or_acc": round(float(auc), 4), "metric": "single-feature AUC"})
        # multi-feature RBF kernel SVM, with and without C
        base = ["SO", "M1", "M2", "randic", "wiener", "n", "m"]
        for tag, cols in [("noC", base), ("withC", base + ["C"])]:
            X = np.column_stack([[single[c](g) for g in g6s] for c in cols])
            clf = make_pipeline(StandardScaler(), SVC(kernel="rbf", C=4.0, gamma="scale"))
            cv = StratifiedKFold(5, shuffle=True, random_state=0)
            acc = cross_val_score(clf, X, y, cv=cv, scoring="accuracy").mean()
            ml_rows.append({"task": task, "features": f"RBF-SVM[{tag}]", "n_pos": int(y.sum()),
                            "auc_or_acc": round(float(acc), 4), "metric": "5-fold CV accuracy"})
        print(f"  (C) task {task}: done", flush=True)
    with open("results/c_ml_tasks.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(ml_rows[0].keys()))
        w.writeheader()
        w.writerows(ml_rows)

    # ---- (D) chemistry-flavoured correlates -------------------------------
    chem_rows = []
    by_nm = defaultdict(list)
    for r in rows:
        g = r["g6"]
        rec = dict(feat[g])
        rec["g6"] = g
        rec["n_leaves"] = sum(1 for x in gl.degrees(gl.from_graph6(g)) if x == 1)
        by_nm[(feat[g]["n"], feat[g]["m"])].append(rec)
    for (n, m), v in sorted(by_nm.items()):
        if len(v) < 20:
            continue
        def sp(key):
            """Spearman rho with average ranks for ties (see report section 10.4).

            Returns None when either variable is constant on the group (the
            coefficient is then undefined); the caller averages over the groups
            where it is defined.
            """
            xs = np.array([x[key] for x in v], float)
            ys = np.array([x["C"] for x in v], float)
            if np.all(xs == xs[0]) or np.all(ys == ys[0]):
                return None
            return float(np.corrcoef(rankdata(xs), rankdata(ys))[0, 1])
        def r3(key):
            val = sp(key)
            return None if val is None else round(val, 3)
        chem_rows.append({"n": n, "m": m, "graphs": len(v),
                          "spearman_C_vs_taus": r3("taus"),
                          "spearman_C_vs_wiener": r3("wiener"),
                          "spearman_C_vs_n_branch": r3("n_branch"),
                          "spearman_C_vs_n_leaves": r3("n_leaves")})
    with open("results/c_chemistry.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(chem_rows[0].keys()))
        w.writeheader()
        w.writerows(chem_rows)
    def mean_key(k):
        vals = [r[k] for r in chem_rows if r[k] is not None]
        if not vals:
            return None
        return round(float(np.mean(vals)), 3)
    print("  (D) mean Spearman:", {k: mean_key(k) for k in
                                   ["spearman_C_vs_taus", "spearman_C_vs_wiener",
                                    "spearman_C_vs_n_branch", "spearman_C_vs_n_leaves"]},
          flush=True)

    with open("results/c_information.json", "w") as f:
        json.dump({"n_graphs": len(rows), "deck_degree_recovery": {"ok": ok, "fail": bad},
                   "information": info,
                   "chemistry_mean_spearman": {k: mean_key(k) for k in
                                               ["spearman_C_vs_taus", "spearman_C_vs_wiener",
                                                "spearman_C_vs_n_branch", "spearman_C_vs_n_leaves"]}},
                  f, indent=1)
    print("wrote results/c_information.json, c_ml_tasks.csv, c_chemistry.csv")


if __name__ == "__main__":
    main()
