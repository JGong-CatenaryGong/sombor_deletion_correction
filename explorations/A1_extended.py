"""
A1-extended (final): a complete deck-only reconstruction of the ordered edge-type
counts N_xy for every graph with m >= 4 (stars included).

Algorithm
  1. degree sequence from the deck (Lemma 2 of explorations/A1_proof.md, valid
     whenever Delta < m);  stars (Delta = m) are recognised from the deck.
  2. the deletion identity
        LHS_xy := sum_e N_xy(G-e) = (m-s+1) N_xy + x N_{x+1,y} + y N_{x,y+1},
     s = x+y, determines every cell with s <= m from the cells of level s+1,
     and N_xy = 0 for s > m+1 (degree-sum lemma).
  3. cells on the free level s = m+1 (coefficient 0) are the only unknowns, and
     there is at most one per row:  u_x := N_{x,m+1-x},  x = m+1-Delta ... Delta
     (e = 2*Delta - m unknowns).  Rows are processed downwards carrying affine
     forms in the unknowns; the degree-sequence identities
        sum_y N_xy = x * n_x      (row sums)      and
        sum_x N_xy = y * n_y      (column sums)
     give 2*Delta exact rational equations for the e unknowns, solved by exact
     Gaussian elimination and checked for integrality/non-negativity.
  4. verification: the recovered N is compared with the true N for every graph
     of the frozen dataset with m >= 4 (both regimes: 2*Delta <= m and 2*Delta > m).
"""
import os
import sys
import gzip
import json
from fractions import Fraction
from collections import Counter

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


def degree_seq_from_deck(cards, m):
    """Lemma 2.  Returns (n_x dict for x>=1, X, n_total) or (None, X, None)."""
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


# ---------- exact linear algebra over Fraction ----------
def solve_linear(eqs, nvars):
    """eqs: list of (rhs, {var: coeff}).  Returns (solution list, status)."""
    rows = []
    for rhs, coeffs in eqs:
        row = [Fraction(coeffs.get(j, 0)) for j in range(nvars)] + [Fraction(rhs)]
        rows.append(row)
    piv = {}
    r = 0
    for c in range(nvars):
        p = None
        for i in range(r, len(rows)):
            if rows[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        pv = rows[r][c]
        rows[r] = [v / pv for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        piv[c] = r
        r += 1
    # consistency
    for i in range(r, len(rows)):
        if all(v == 0 for v in rows[i][:nvars]) and rows[i][nvars] != 0:
            return None, "inconsistent"
    if len(piv) < nvars:
        return None, f"underdetermined(rank {len(piv)}/{nvars})"
    sol = [Fraction(0)] * nvars
    for c, i in piv.items():
        sol[c] = rows[i][nvars]
    return sol, "unique"


def solve_extended(m, Delta, n_x, LHS):
    """Deck-only recovery of N.  Returns (N dict, form dict, status)."""
    sym_of_row = {}
    forms = {}                    # (x,y) -> (const, {sym: coeff}) as Fractions
    eqs = []
    for x in range(Delta, 0, -1):
        ytop = min(Delta, m + 1 - x)
        freesym = None
        if x + ytop == m + 1:
            freesym = len(sym_of_row)
            sym_of_row[x] = freesym
        for y in range(ytop, 0, -1):
            if freesym is not None and y == ytop:
                forms[(x, y)] = (Fraction(0), {freesym: Fraction(1)})
                continue
            s = x + y
            coef = m - s + 1
            if coef <= 0:
                return None, None, "coef<=0"
            c0 = Fraction(LHS.get((x, y), 0))
            cs = {}
            a0, ad = forms.get((x + 1, y), (Fraction(0), {}))
            c0 -= x * a0
            for k, v in ad.items():
                cs[k] = cs.get(k, Fraction(0)) - x * v
            if y + 1 <= ytop:
                b0, bd = forms.get((x, y + 1), (Fraction(0), {}))
                c0 -= y * b0
                for k, v in bd.items():
                    cs[k] = cs.get(k, Fraction(0)) - y * v
            forms[(x, y)] = (c0 / coef, {k: v / coef for k, v in cs.items() if v != 0})
        # row-sum equation  sum_y N_xy = x * n_x
        r0 = Fraction(0)
        rd = {}
        for y in range(1, ytop + 1):
            a, d = forms[(x, y)]
            r0 += a
            for k, v in d.items():
                rd[k] = rd.get(k, Fraction(0)) + v
        eqs.append((Fraction(x * n_x.get(x, 0)) - r0, rd))
    # column-sum equations  sum_x N_xy = y * n_y
    for y in range(1, Delta + 1):
        r0 = Fraction(0)
        rd = {}
        for x in range(1, Delta + 1):
            if (x, y) in forms:
                a, d = forms[(x, y)]
                r0 += a
                for k, v in d.items():
                    rd[k] = rd.get(k, Fraction(0)) + v
        eqs.append((Fraction(y * n_x.get(y, 0)) - r0, rd))
    nvars = len(sym_of_row)
    if nvars == 0:
        sol, status = [], "unique"
    else:
        sol, status = solve_linear(eqs, nvars)
        if sol is None:
            return None, None, status
    N = {}
    for (x, y), (a, d) in forms.items():
        v = a + sum(c * sol[k] for k, c in d.items())
        if v.denominator != 1:
            return None, None, "nonintegral"
        if v < 0:
            return None, None, "negative"
        N[(x, y)] = int(v)
    return N, forms, ("ok" if nvars == 0 else f"ok({nvars} free)")


def main():
    fam = Counter()
    stats = Counter()
    by_family = {}
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
            regime = "deg" if 2 * Delta > m else "nondeg"
            n_checked += 1
            cards = cards_of(adj)
            LHS = lhs_matrix(cards)
            truth = ordered_N(adj)

            if Delta == m:                                  # star
                okstar = (truth.get((1, m), 0) == m and truth.get((m, 1), 0) == m
                          and len(truth) == 2)
                stats["star_ok" if okstar else "star_fail"] += 1
                fam[(regime, m - Delta)] = fam.get((regime, m - Delta), 0) + 1
                if not okstar:
                    failures.append((r["g6"], "star"))
                continue

            n_x, X, ntot = degree_seq_from_deck(cards, m)
            if n_x is None or X != Delta:
                stats["lemma2_fail"] += 1
                failures.append((r["g6"], "lemma2"))
                continue
            # degree-sequence correctness (including isolated vertices)
            ds_rec = sorted([x for x, c in n_x.items() for _ in range(c)],
                            reverse=True) + [0] * (ntot - sum(n_x.values()))
            if ds_rec != sorted(deg, reverse=True):
                stats["lemma2_mismatch"] += 1
                failures.append((r["g6"], "lemma2-mismatch"))
                continue
            N, forms, status = solve_extended(m, Delta, n_x, LHS)
            if N is None:
                stats[f"solve_fail:{status}"] += 1
                failures.append((r["g6"], f"solve-{status}"))
                continue
            bad = [(x, y, N.get((x, y), 0), truth.get((x, y), 0))
                   for x in range(1, Delta + 1) for y in range(1, Delta + 1)
                   if N.get((x, y), 0) != truth.get((x, y), 0)]
            # cells with x>Delta or y>Delta are zero by definition
            if bad:
                stats["mismatch"] += 1
                failures.append((r["g6"], f"mismatch {bad[:3]}"))
            else:
                stats["ok"] += 1
                key = (regime, m - Delta)
                by_family.setdefault(key, Counter())[status] += 1

    out = {
        "script": "explorations/A1_extended.py",
        "dataset": "frozen n<=9, all graphs with m>=4",
        "n_checked": n_checked,
        "outcomes": dict(stats),
        "success_rate": (stats["ok"] + stats["star_ok"]) / n_checked,
        "free_parameter_profile": {"%s/k=%d" % k: dict(v) for k, v in sorted(by_family.items())},
        "failures": failures[:20],
        "n_failures": len(failures),
    }
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    with open(os.path.join(HERE, "results", "A1_extended.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: out[k] for k in ("n_checked", "outcomes", "success_rate", "n_failures")},
                     indent=1))
    print("wrote explorations/results/A1_extended.json")


if __name__ == "__main__":
    main()
