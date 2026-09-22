"""
A1 task 1.2 -- structure of the degenerate family {m >= 4, 2*Delta > m} and
refinement-invariant separation tests.

Context: the edge-type linear system (explorations/deck_edgetype_system.py,
identity verified with 0 violations on all 288,208 graphs with m >= 4) recovers
all ordered edge-type counts N_xy exactly when 2*Delta <= m (286,364 graphs).
The remaining 1,844 graphs (2*Delta > m) have free rows at level x+y = m+1 and
a shadow cascade, so the system alone leaves information undetermined.

This script analyses that degenerate family (read-only on the frozen dataset):
  * structural taxonomy: star (Delta = m) vs near-star; number of vertices with
    degree > m/2; pairwise adjacency of high-degree vertices; m - Delta;
  * which true N values fall into undetermined cells;
  * separation tests WITHIN the family: do the deck-derived statistics
      (i)   LHS matrix (sums of card edge-type counts),
      (ii)  LHS + degree sequence,
      (iii) multiset of per-card N-matrices (strictly stronger deck statistic),
    separate all distinct edge-type count vectors N?  (0 collisions would mean
    the deck information suffices empirically even where the linear system
    degenerates.)

Output: explorations/results/A1_degenerate.json
"""
import os
import sys
import gzip
import json
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "src"))
import graphlib as gl


# --- self-contained copies of the identity machinery (do not import, to keep
# --- this analysis independent of the verification script's file layout) ---
def card_sums_and_N(adj):
    m = gl.n_edges(adj)
    d = gl.degrees(adj)
    N = Counter()
    for u, v in gl.edges_of(adj):
        N[(d[u], d[v])] += 1
        N[(d[v], d[u])] += 1
    LHS = Counter()
    for u, v in gl.edges_of(adj):
        c = list(adj)
        c[u] &= ~(1 << v)
        c[v] &= ~(1 << u)
        t = tuple(c)
        cd = gl.degrees(t)
        for a, b in gl.edges_of(t):
            LHS[(cd[a], cd[b])] += 1
            LHS[(cd[b], cd[a])] += 1
    return m, max(d), N, LHS


def recover(m, LHS, Delta):
    R = Counter()
    free = []
    for s in range(m + 1, -1, -1):
        for x in range(0, s + 1):
            y = s - x
            if x > Delta or y > Delta:
                R[(x, y)] = 0
                continue
            coef = m - s + 1
            lhs = LHS.get((x, y), 0)
            if coef == 0:
                if lhs != 0:
                    return None, free, ("violation", (x, y), lhs)
                free.append((x, y))
                R[(x, y)] = None
            else:
                a = R[(x + 1, y)]
                b = R[(x, y + 1)]
                if a is None or b is None:
                    R[(x, y)] = None
                else:
                    val = (lhs - x * a - y * b) / coef
                    if val != int(val) or val < 0:
                        return None, free, ("noninteger", (x, y), val)
                    R[(x, y)] = int(val)
    return R, free, None


def card_N_matrices(adj):
    """Multiset (sorted tuple) of per-card ordered edge-type count matrices."""
    mats = []
    for u, v in gl.edges_of(adj):
        c = list(adj)
        c[u] &= ~(1 << v)
        c[v] &= ~(1 << u)
        t = tuple(c)
        cd = gl.degrees(t)
        cn = Counter()
        for a, b in gl.edges_of(t):
            cn[(cd[a], cd[b])] += 1
            cn[(cd[b], cd[a])] += 1
        mats.append(tuple(sorted(cn.items())))
    return tuple(sorted(mats))


def main():
    recs = []
    with gzip.open(os.path.join(ROOT, "results", "graphs.jsonl.gz"), "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["m"] >= 4:
                ds = [int(x) for x in r["ds"].split(",")]
                if 2 * max(ds) > r["m"]:
                    recs.append(r)
    print(f"degenerate graphs (m>=4, 2*Delta>m): {len(recs)}", flush=True)

    stats = Counter()
    m_minus_delta = Counter()
    n_hi_dist = Counter()
    examples = []
    sep = {"lhs": {}, "lhs_ds": {}, "cards": {}}
    sep_collisions = {"lhs": [], "lhs_ds": [], "cards": []}

    for r in recs:
        adj = gl.from_graph6(r["g6"])
        n = len(adj)
        m, Delta, N, LHS = card_sums_and_N(adj)
        R, free, status = recover(m, LHS, Delta)
        assert status is None, (r["g6"], status)
        d = gl.degrees(adj)
        hi = [v for v in range(n) if 2 * d[v] > m]
        hi_pairwise_adj = all((adj[u] >> v) & 1 for u in hi for v in hi if u != v)
        undet = [k for k, v in R.items() if v is None]
        loses = [k for k in undet if N.get(k, 0) > 0]

        stats["total"] += 1
        stats["star_Delta_eq_m"] += int(Delta == m)
        stats["unique_maxdeg_vertex"] += int(list(d).count(Delta) == 1)
        stats["hi_pairwise_adjacent"] += int(hi_pairwise_adj)
        stats["undet_nonzero_cells"] += int(bool(loses))
        if Delta == m:
            # genuine star K_{1,m} + isolates?
            ds_sorted = sorted(d, reverse=True)
            stats["true_star"] += int(ds_sorted[: m + 1] == [m] + [1] * m)
        m_minus_delta[m - Delta] += 1
        n_hi_dist[len(hi)] += 1

        Nkey = tuple(sorted(N.items()))
        keys = {
            "lhs": tuple(sorted(LHS.items())),
            "lhs_ds": (tuple(sorted(LHS.items())), r["ds"]),
            "cards": card_N_matrices(adj),
        }
        for name, key in keys.items():
            prev = sep[name].get(key)
            if prev is None:
                sep[name][key] = (r["g6"], Nkey)
            elif prev[1] != Nkey:
                sep_collisions[name].append((prev[0], r["g6"]))

        if len(examples) < 12:
            examples.append({
                "g6": r["g6"], "n": n, "m": m, "Delta": Delta, "ds": r["ds"],
                "n_hi": len(hi), "m_minus_Delta": m - Delta,
                "undet_nonzero": [list(k) for k in loses][:6],
                "true_N_nonzero": [[list(k), v] for k, v in sorted(N.items()) if v][:8],
            })

    out = {
        "script": "explorations/A1_degenerate_analysis.py",
        "family": "n<=9 graphs with m>=4 and 2*Delta > m",
        "n_graphs": stats["total"],
        "stats": dict(stats),
        "m_minus_Delta_distribution": {str(k): v for k, v in sorted(m_minus_delta.items())},
        "n_high_degree_vertices_distribution": {str(k): v for k, v in sorted(n_hi_dist.items())},
        "separation_collisions": {k: v for k, v in sep_collisions.items()},
        "separation_verdict": {
            k: ("separates all distinct N" if not v else f"{len(v)} collisions")
            for k, v in sep_collisions.items()},
        "examples": examples,
    }
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    with open(os.path.join(HERE, "results", "A1_degenerate.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: out[k] for k in
                      ("n_graphs", "stats", "m_minus_Delta_distribution",
                       "n_high_degree_vertices_distribution", "separation_verdict")},
                     indent=1))
    print("wrote explorations/results/A1_degenerate.json")


if __name__ == "__main__":
    main()
