"""
A1-closure: full deck-only reconstruction for the degenerate family 2*Delta > m.

Ingredients (all deck-computable):
  * degree sequence (Lemma 2) and Delta;
  * the deletion identity (back-substitution from level m+1 downwards);
  * the free cells on level m+1: exactly one per row x in [m+1-Delta, Delta];
  * the HUB PROFILE: for a unique max-degree vertex v whose second-largest degree
    is <= Delta-2, every card in which v has degree Delta-1 has v as its unique
    top vertex, so reading v's neighbour degrees there and summing over the Delta
    such cards gives (Delta-1) * P, where P is the true neighbour-degree multiset
    of v (each neighbour is missing from exactly one card).  P pins the top free
    cell u_Delta = #{z in N(v) : d_z = m+1-Delta}.
    Multi-hub graphs are handled by summing the two profiles read from a card in
    which both hubs keep degree Delta.
    Ambiguous cards (several degree-(Delta-1) vertices) are resolved by searching
    the candidate assignment that makes the aggregate divisible by Delta-1 with
    |P| = Delta.
  * lower free rows are determined by their row-sum identity sum_y N_xy = x n_x
    (when non-degenerate), else reported unresolved.
Verification: exact comparison with the true N over the whole range x,y <= Delta.
"""
import os
import sys
import gzip
import json
from fractions import Fraction
from collections import Counter
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "src"))
import graphlib as gl


def ordered_N(adj):
    d = gl.degrees(adj)
    N = Counter()
    for u, v in gl.edges_of(adj):
        N[(d[u], d[v])] += 1
        N[(d[v], d[u])] += 1
    return N


def cards_of(adj):
    out = []
    for u, v in gl.edges_of(adj):
        c = list(adj)
        c[u] &= ~(1 << v)
        c[v] &= ~(1 << u)
        out.append(tuple(c))
    return out


def lhs_matrix(cards):
    LHS = Counter()
    for c in cards:
        LHS.update(ordered_N(c))
    return LHS


def neighbors(adj, v):
    return [i for i in range(len(adj)) if (adj[v] >> i) & 1]


def degree_seq_from_deck(cards, m):
    c_x = Counter()
    for c in cards:
        for d in gl.degrees(c):
            c_x[d] += 1
    X = max(c_x) if c_x else 0
    total = sum(c_x.values()) // m if m else 0
    n = {X + 1: 0}
    for x in range(X, 0, -1):
        num = c_x.get(x, 0) - (x + 1) * n[x + 1]
        den = m - x
        if den <= 0 or num % den or num // den < 0:
            return None, X, None
        n[x] = num // den
    return n, X, total


def read_profile(cards, Delta, n_hubs):
    """Return (P_sum, status): total neighbour-degree profile over the hubs (sum
    of both hubs' profiles for a double hub)."""
    k = Delta - 1
    if k == 0:
        return None, "k=0"
    parts = []
    for c in cards:
        d = gl.degrees(c)
        mx = max(d)
        if mx != Delta - 1 and not (n_hubs == 2 and mx == Delta):
            continue
        if n_hubs == 2 and mx == Delta:
            verts = [i for i in range(len(d)) if d[i] == Delta]
            if len(verts) != 2:
                continue
            prof = Counter()
            for v in verts:
                prof.update(d[x] for x in neighbors(c, v))
            parts.append(("both", prof))
            continue
        verts = [i for i in range(len(d)) if d[i] == Delta - 1]
        parts.append(("cand", [Counter(d[x] for x in neighbors(c, v)) for v in verts]))
    if n_hubs == 2:
        both = [p for kind, p in parts if kind == "both"]
        if both:
            return both[0], "double-hub"
        return None, "no-both-card"
    cand = [p for kind, p in parts if kind == "cand"]
    if len(cand) != Delta:
        return None, f"ncards={len(cand)}"
    # search one candidate per card such that the aggregate is divisible by k and has size Delta
    if any(len(p) > 6 for p in cand):
        return None, "too-many-candidates"
    for choice in product(*[range(len(p)) for p in cand]):
        agg = Counter()
        for idx, p in zip(choice, cand):
            agg.update(p[idx])
        if all(cnt % k == 0 for cnt in agg.values()) and sum(agg.values()) // k == Delta:
            P = Counter({val: cnt // k for val, cnt in agg.items()})
            return P, "unique-hub"
    return None, "no-consistent-assignment"


def solve_with_pinned(m, Delta, n_x, LHS, pinned):
    """Row-by-row affine substitution; free cells pinned when known, else from the
    row-sum identity.  Returns (N, unresolved list, status)."""
    N = {}
    unresolved = []
    free_rows = []
    for x in range(Delta, 0, -1):
        ytop = min(Delta, m + 1 - x)
        free = (x + ytop == m + 1)
        a = {}
        b = {}
        if free:
            if x in pinned:
                a[ytop], b[ytop] = pinned[x], 0
            else:
                a[ytop], b[ytop] = 0, 1
        for y in range(ytop, 0, -1):
            if free and y == ytop:
                continue
            s = x + y
            coef = m - s + 1
            if coef <= 0:
                return None, [], "coef<=0"
            ra = LHS.get((x, y), 0) - x * N.get((x + 1, y), 0)
            rb = 0
            if y + 1 <= ytop:
                ra -= y * a.get(y + 1, 0)
                rb -= y * b.get(y + 1, 0)
            if ra % coef or rb % coef:
                return None, [], "nonintegral"
            a[y], b[y] = ra // coef, rb // coef
            if not free and (a[y] < 0 or b[y] != 0):
                return None, [], "bad-value"
        if not free:
            for y in range(ytop, 0, -1):
                N[(x, y)] = a[y]
            continue
        if x in pinned:
            vals = {y: a[y] for y in range(1, ytop + 1)}
        else:
            sa = sum(a.get(y, 0) for y in range(1, ytop + 1))
            sb = sum(b.get(y, 0) for y in range(1, ytop + 1))
            target = x * n_x.get(x, 0)
            if sb == 0:
                if sa != target:
                    return None, [], "rowsum-conflict"
                unresolved.append(x)
                vals = {y: a.get(y, 0) for y in range(1, ytop + 1)}
            else:
                if (target - sa) % sb:
                    return None, [], "rowsum-nonintegral"
                u = (target - sa) // sb
                vals = {y: a.get(y, 0) + b.get(y, 0) * u for y in range(1, ytop + 1)}
                if any(v < 0 for v in vals.values()):
                    return None, [], "negative-cell"
        for y in range(1, ytop + 1):
            if vals.get(y, 0) < 0:
                return None, [], "negative-cell"
            N[(x, y)] = vals.get(y, 0)
    return N, unresolved, "ok"


def main():
    stats = Counter()
    failures = []
    n_checked = 0
    with gzip.open(os.path.join(ROOT, "results", "graphs.jsonl.gz"), "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["m"] < 4:
                continue
            adj = gl.from_graph6(r["g6"])
            deg = gl.degrees(adj)
            m = r["m"]
            Delta = max(deg)
            if 2 * Delta <= m:
                continue                     # already covered by the main theorem
            n_checked += 1
            truth = ordered_N(adj)
            cards = cards_of(adj)
            LHS = lhs_matrix(cards)

            if Delta == m:                   # star
                okstar = (truth.get((1, m), 0) == m and truth.get((m, 1), 0) == m
                          and len(truth) == 2)
                stats["star_ok" if okstar else "star_fail"] += 1
                continue

            n_x, X, ntot = degree_seq_from_deck(cards, m)
            if n_x is None or X != Delta:
                stats["lemma2_fail"] += 1
                continue
            n_hubs = sum(1 for d in deg if d == Delta)
            P, pstatus = read_profile(cards, Delta, n_hubs)
            pinned = {}
            if P is not None:
                val = P.get(m + 1 - Delta, 0)
                pinned[Delta] = val
            N, unresolved, status = solve_with_pinned(m, Delta, n_x, LHS, pinned)
            if N is None:
                stats[f"solve_fail:{status}"] += 1
                failures.append((r["g6"], f"solve-{status}"))
                continue
            bad = [(x, y, N.get((x, y), 0), truth.get((x, y), 0))
                   for x in range(1, Delta + 1) for y in range(1, Delta + 1)
                   if N.get((x, y), 0) != truth.get((x, y), 0)]
            if bad:
                stats["mismatch"] += 1
                failures.append((r["g6"], f"mismatch {bad[:3]}"))
            elif unresolved:
                stats[f"ok-but-unresolved:{len(unresolved)}"] += 1
                failures.append((r["g6"], f"unresolved rows {unresolved}"))
            else:
                stats["ok"] += 1
                stats[f"ok/{pstatus}"] += 1

    out = {
        "script": "explorations/A1_closure.py",
        "family": "{n<=9, m>=4, 2*Delta > m}",
        "n_graphs": n_checked,
        "outcomes": dict(stats),
        "n_failures": len(failures),
        "failures": failures[:15],
    }
    with open(os.path.join(HERE, "results", "A1_closure.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
