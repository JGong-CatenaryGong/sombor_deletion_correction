"""
explorations/deck_edgetype_system.py -- feasibility check for closing the
conditional proposition of report section 7.2.

Identity under test (double counting; derivation in 探索方向.md, A1):

    Let N_xy(G) = # ordered edges (u,v) with d_u = x, d_v = y  (N_xy = N_yx).
    For every graph G with m edges and maximum degree Delta:

        sum_{e in E} N_xy(G - e) = (m - x - y + 1) N_xy + x N_{x+1,y} + y N_{x,y+1}.

  * The left side is computable from the edge deck alone (card degree
    sequences are isomorphism-invariant).
  * Boundary knowledge from the deck: Delta = max card degree, hence
    N_xy = 0 whenever x > Delta or y > Delta; also N_xy = 0 for x+y > m+1
    (d_u + d_v <= m + 1 for every edge, report 8.3 step 2).
  * Back-substitution in decreasing x+y: rows with x+y = m+1 have coefficient
    0 (free); a row is undetermined iff some (x,y) with x,y <= Delta and
    x+y = m+1 can be reached from it by (+1, 0)/(0, +1) steps, which happens
    exactly when 2*Delta >= m+1.
  * THEOREM CANDIDATE: if m >= 4 and 2*Delta <= m, the edge deck determines
    the edge-type multiset, hence SO(G) and the 11 other edge-additive degree
    indices are edge-reconstructible.

This script checks on all n <= 9 graphs with m >= 4:
  (a) the identity holds row by row;
  (b) back-substitution never produces non-integers/negatives and matches the
      true counts on every determined row;
  (c) the set of graphs with full recovery equals exactly {2*Delta <= m};
  (d) whether the multiset of card edge-type matrices (the left sides) already
      separates all distinct N (no two graphs share LHS with different N).
"""
import os, sys, gzip, json
from collections import Counter
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import graphlib as gl

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


def card_sums_and_N(adj):
    n = len(adj)
    m = gl.n_edges(adj)
    if m < 4:
        return None
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
    """Back-substitute in decreasing x+y.

    Returns (R, free_rows, status) where R[(x,y)] is int (determined),
    0 (boundary-known zero) or None (undetermined shadow of a free row);
    status is None on success or a ('violation'|'noninteger', ...) tuple.
    """
    R = Counter()
    free = []
    for s in range(m + 1, -1, -1):
        for x in range(0, s + 1):
            y = s - x
            if x > Delta or y > Delta:
                R[(x, y)] = 0            # boundary: no such edges exist
                continue
            coef = m - s + 1
            lhs = LHS.get((x, y), 0)
            if coef == 0:
                if lhs != 0:             # the identity must give 0 here
                    return None, free, ("violation", (x, y), lhs)
                free.append((x, y))
                R[(x, y)] = None
            else:
                a = R[(x + 1, y)]        # level s+1, already processed
                b = R[(x, y + 1)]
                if a is None or b is None:
                    R[(x, y)] = None     # shadow of a free row
                else:
                    val = (lhs - x * a - y * b) / coef
                    if val != int(val) or val < 0:
                        return None, free, ("noninteger", (x, y), val)
                    R[(x, y)] = int(val)
    return R, free, None


def main():
    recs = []
    with gzip.open(os.path.join(ROOT, "results", "graphs.jsonl.gz"), "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["m"] >= 4:
                recs.append(r["g6"])
    print(f"{len(recs)} graphs with m >= 4", flush=True)

    n_identity_viol = 0
    n_noninteger = 0
    n_mismatch = 0
    full_recovery = 0          # no undetermined cell within the Delta-range
    full_recovery_expected = 0  # 2*Delta <= m
    inconsistent_pred = []     # recovery outcome disagrees with the criterion
    undetermined_loses_info = 0
    by_lhs = {}
    lhs_collisions = []
    deg_examples = []

    for i, g6 in enumerate(recs):
        adj = gl.from_graph6(g6)
        res = card_sums_and_N(adj)
        if res is None:
            continue
        m, Delta, N, LHS = res
        R, free_rows, status = recover(m, LHS, Delta)
        if status is not None:
            if status[0] == "violation":
                n_identity_viol += 1
            else:
                n_noninteger += 1
            continue
        # (b) determined rows must match the truth
        for k, v in R.items():
            if v is None:
                continue
            if v != N.get(k, 0):
                n_mismatch += 1
                print("MISMATCH", g6, k, v, N.get(k, 0))
        # (c) full recovery <=> 2*Delta <= m
        undet = [k for k, v in R.items() if v is None]
        got_full = not undet
        expected_full = 2 * Delta <= m
        if got_full:
            full_recovery += 1
        if expected_full:
            full_recovery_expected += 1
        if got_full != expected_full:
            inconsistent_pred.append((g6, m, Delta, undet[:4]))
        loses = [k for k in undet if N.get(k, 0) > 0]
        if loses:
            undetermined_loses_info += 1
            if len(deg_examples) < 8:
                deg_examples.append((g6, m, Delta, loses[:6]))
        # (d) weak invariant: LHS matrix separation
        key = tuple(sorted(LHS.items()))
        if key in by_lhs:
            if by_lhs[key][1] != N:
                lhs_collisions.append((by_lhs[key][0], g6))
        else:
            by_lhs[key] = (g6, N)
        if (i + 1) % 50000 == 0:
            print(f"  {i+1}/{len(recs)}", flush=True)

    print(f"\nidentity violations:            {n_identity_viol}")
    print(f"non-integer/negative results:   {n_noninteger}")
    print(f"determined-row mismatches:      {n_mismatch}")
    print(f"graphs with full recovery:      {full_recovery}")
    print(f"graphs with 2*Delta <= m:       {full_recovery_expected}")
    print(f"prediction inconsistencies:     {len(inconsistent_pred)}")
    for g, mm, dd, u in inconsistent_pred[:5]:
        print(f"   {g} m={mm} Delta={dd} undet={u}")
    print(f"graphs whose undetermined rows hide nonzero true counts: "
          f"{undetermined_loses_info}")
    for g, mm, dd, ls in deg_examples:
        print(f"   {g} m={mm} Delta={dd} loses={ls}")
    print(f"LHS collisions with different N: {len(lhs_collisions)}")
    for a, b in lhs_collisions[:5]:
        print(f"   collision: {a} vs {b}")


if __name__ == "__main__":
    main()
