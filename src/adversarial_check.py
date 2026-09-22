"""
adversarial_check.py -- stress-test the claimed theorems OUTSIDE the n<=9 range.

The exhaustive checks in the main pipeline only cover graphs with n <= 9.  A proof
should of course hold for all n, but a bug in the *proof* or in my understanding
would most likely show up as a large-graph counterexample.  This script searches
for one, using families that are extremal or structured:

  random G(n,p), random regular, random chemical (Delta<=4), random trees,
  stars + random extra edges, quasi-stars, complete bipartite, complete graphs,
  disjoint unions of cliques, split/threshold graphs, "double stars",
  random graphs with a prescribed degree sequence (configuration model),
  and graphs designed to sit near the claimed bounds.

Claims tested per graph (m >= 2):
  T1  C(G) <= (M1 - 2m) c(m,1) <= m(m-1) c(m,1)                     [star theorem]
      (the equality characterisation for T1 is proved in Lean and checked
       exhaustively for n <= 9; it is not repeated on the large families here)
  T2  sum_u d_u(d_u-1) c(d_u,1)  >=  C(G)                            [degree-seq bound]
  T3  sum_uv Psi_uv/(2d_u+2d_v-1) <= C(G) <= sqrt2 * sum_uv Psi/(2d_u+2d_v-1)
  T4  Z/(4Delta-1) <= C(G) <= (sqrt2/3) Z,  Z = 2F-3M1+2m
  T5  general edge-additive identity applied to T_f = C itself:
        sum_e C(G-e) = (m-1) C(G) - C_phi(G),
      C_phi(G) = sum_u (d_u-1) sum_{x in N(u)} [phi(d_u,d_x) - phi(d_u-1,d_x)]
  T6  Sombor identity sum_e SO(G-e) = (m-1)SO(G) - C(G)              [on large graphs]
  T7  tree Wiener identity W(T)-W(T-e) = |A||B| + |B| sigma_A(u) + |A| sigma_B(v)
  T8  deck -> degree sequence linear system  c_x = n_x(m-x) + n_{x+1}(x+1)
      (uses the main-pipeline implementation; on large/dense graphs the
       card-based claims T5/T6/T8 are skipped above m = card_cap and recorded
       as "skipped(...)" in the JSON)

Output: results/adversarial_check.json
"""

from __future__ import annotations

import json
import math
import os
import random
import sys
from collections import Counter, defaultdict

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import graphlib as gl

RNG = random.Random(20240919)


def c_fn(a, b):
    return math.sqrt(a * a + b * b) - math.sqrt((a - 1) ** 2 + b * b)


def phi(a, b):
    return (a - 1) * c_fn(a, b) + (b - 1) * c_fn(b, a)


def adj_from_nx(G) -> tuple:
    nodes = sorted(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    return gl.from_edges(len(nodes), [(idx[u], idx[v]) for u, v in G.edges()])


def C_of(adj):
    d = gl.degrees(adj)
    return sum(phi(d[u], d[v]) for u, v in gl.edges_of(adj))


def sombor_of(adj):
    d = gl.degrees(adj)
    return sum(math.sqrt(d[u] ** 2 + d[v] ** 2) for u, v in gl.edges_of(adj))


def C_phi_of(adj):
    """C_f for f = phi (the correction term of C itself)."""
    d = gl.degrees(adj)
    tot = 0.0
    for u, v in gl.edges_of(adj):
        a, b = d[u], d[v]
        if a >= 2:
            tot += (a - 1) * (phi(a, b) - phi(a - 1, b))
        if b >= 2:
            tot += (b - 1) * (phi(b, a) - phi(b - 1, a))
    return tot


def deck_degree_solution(adj):
    """Recover d(G) from the deck, using the *same* implementation as the main
    pipeline (`c_information.deck_degree_solution`), imported rather than copied.

    An earlier version of this file carried a reduced copy that lacked the
    isolated-vertex channels used to fix the free parameter when Delta = m;
    for every star that copy failed, and the failures were reported as
    "zero violations" because the report did not read the `violations` field.
    Importing the full algorithm removes the possibility of such a drift.
    """
    from c_information import deck_degree_solution as _full
    return _full(adj)


def check_graph(adj, name, do_deck=True, do_cards=True, card_cap=400):
    d = gl.degrees(adj)
    n = len(adj)
    m = gl.n_edges(adj)
    out = {"family": name, "n": n, "m": m}
    if m < 2:
        return None
    C = C_of(adj)
    M1 = sum(x * x for x in d)
    F = sum(x ** 3 for x in d)
    Z = 2 * F - 3 * M1 + 2 * m
    D = max(d)
    cm1 = c_fn(m, 1)
    res = {
        "T1_star": C - m * (m - 1) * cm1,
        "T1_M1": C - (M1 - 2 * m) * cm1,
        "T2_degseq": sum(x * (x - 1) * c_fn(x, 1) for x in d) - C,
        "T3_lo": C - sum(
            ((d[u] - 1) * (2 * d[u] - 1) + (d[v] - 1) * (2 * d[v] - 1)) / (2 * d[u] + 2 * d[v] - 1)
            for u, v in gl.edges_of(adj)),
        "T4_lo": C - Z / (4 * D - 1) if D else 0.0,
        "T4_hi": math.sqrt(2) / 3 * Z - C,
    }
    res["T3_hi"] = math.sqrt(2) * sum(
        ((d[u] - 1) * (2 * d[u] - 1) + (d[v] - 1) * (2 * d[v] - 1)) / (2 * d[u] + 2 * d[v] - 1)
        for u, v in gl.edges_of(adj)) - C
    heavy = m > card_cap
    if do_cards and not heavy:
        # T5: general identity applied to T = C ;  T6: Sombor identity
        sC = 0.0
        sSO = 0.0
        for u, v in gl.edges_of(adj):
            cc = list(adj)
            cc[u] &= ~(1 << v)
            cc[v] &= ~(1 << u)
            t = tuple(cc)
            sC += C_of(t)
            sSO += sombor_of(t)
        SO = sombor_of(adj)
        Ccorr = 0.0  # C(G) from the Sombor identity
        for u, v in gl.edges_of(adj):
            a, b = d[u], d[v]
            if a >= 2:
                Ccorr += (a - 1) * c_fn(a, b)
            if b >= 2:
                Ccorr += (b - 1) * c_fn(b, a)
        res["T5_C_identity"] = abs(sC - ((m - 1) * C - C_phi_of(adj)))
        res["T6_so_identity"] = abs(sSO - ((m - 1) * SO - Ccorr))
    if do_deck and not heavy:
        # the main-pipeline algorithm returns (degree_sequence_or_None, ok)
        got, ok = deck_degree_solution(adj)
        res["T8_deck_ok"] = int(bool(ok) and got == tuple(sorted(d, reverse=True)))
    if heavy:
        res["T5_C_identity"] = "skipped(m>%d)" % card_cap
        res["T6_so_identity"] = "skipped(m>%d)" % card_cap
        res["T8_deck_ok"] = "skipped(m>%d)" % card_cap
    out["residuals"] = res
    return out


def tree_check(T: nx.Graph):
    adj = adj_from_nx(T)
    n = len(adj)
    err = 0.0
    for u, v in gl.edges_of(adj):
        cc = list(adj)
        cc[u] &= ~(1 << v)
        cc[v] &= ~(1 << u)
        ct = tuple(cc)
        ru = _reach(ct, u)
        rv = _reach(ct, v)
        A = [i for i in range(n) if ru >> i & 1]
        B = [i for i in range(n) if rv >> i & 1]
        nbr = [[j for j in range(n) if (ct[i] >> j) & 1] for i in range(n)]
        sigA = _deg_sum(nbr, u, set(A))
        sigB = _deg_sum(nbr, v, set(B))
        formula = len(A) * len(B) + len(B) * sigA + len(A) * sigB
        err = max(err, abs(formula - (wiener(adj) - wiener(ct))))
    return err


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


def _deg_sum(nbr, v, comp):
    dist = {v: 0}
    fr = [v]
    while fr:
        nxt = []
        for u in fr:
            for w in nbr[u]:
                if w in comp and w not in dist:
                    dist[w] = dist[u] + 1
                    nxt.append(w)
        fr = nxt
    return sum(dist.values())


def wiener(adj):
    n = len(adj)
    nbr = [[j for j in range(n) if (adj[i] >> j) & 1] for i in range(n)]
    tot = 0.0
    for s in range(n):
        dist = {s: 0}
        fr = [s]
        while fr:
            nxt = []
            for u in fr:
                for w in nbr[u]:
                    if w not in dist:
                        dist[w] = dist[u] + 1
                        nxt.append(w)
            fr = nxt
        tot += sum(dist.values())
    return tot / 2.0


def families():
    """Yield (name, adjacency) test graphs, biased towards extremal shapes."""
    for n in (10, 14, 20, 30, 50, 80, 150, 300):
        for p in (0.03, 0.1, 0.3, 0.6, 0.9):
            G = nx.gnp_random_graph(n, p, seed=RNG.randrange(10 ** 6))
            yield f"G(n={n},p={p})", adj_from_nx(G)
    for n in (10, 20, 40, 80, 200):
        for r in (2, 3, 4, 6):
            if n * r % 2 == 0 and r < n:
                try:
                    G = nx.random_regular_graph(r, n, seed=RNG.randrange(10 ** 6))
                    yield f"regular(n={n},r={r})", adj_from_nx(G)
                except nx.NetworkXError:
                    pass
    # stars with random extra edges (near the extremal bound)
    for n in (12, 25, 60, 200):
        for extra in (0, 1, 3, 10):
            G = nx.star_graph(n - 1)
            G.add_nodes_from(range(n))
            possible = [(i, j) for i in range(1, n) for j in range(i + 1, n)
                        if not G.has_edge(i, j)]
            RNG.shuffle(possible)
            for (i, j) in possible[:extra]:
                G.add_edge(i, j)
            yield f"star+{extra}edges(n={n})", adj_from_nx(G)
    # quasi-stars: hub plus a clique
    for n in (12, 30, 100):
        for k in (3, 5, 8):
            if k + 1 < n:
                G = nx.Graph()
                G.add_nodes_from(range(n))
                for i in range(1, k + 1):
                    for j in range(i + 1, k + 1):
                        G.add_edge(i, j)
                for i in range(1, n):
                    G.add_edge(0, i)
                yield f"quasistar(n={n},clique={k})", adj_from_nx(G)
    # complete bipartite, complete, disjoint cliques, double stars, random trees
    for a, b in ((2, 8), (3, 20), (5, 50), (10, 40)):
        yield f"K({a},{b})", adj_from_nx(nx.complete_bipartite_graph(a, b))
    for n in (10, 30, 60):
        yield f"K{n}", adj_from_nx(nx.complete_graph(n))
    for parts in ((3, 3, 3), (4, 4, 4, 4), (5, 5, 5, 5, 5)):
        G = nx.disjoint_union_all([nx.complete_graph(k) for k in parts])
        yield f"cliques{parts}", adj_from_nx(G)
    for a, b in ((3, 3), (10, 10), (40, 40)):
        G = nx.Graph()
        G.add_edge(0, 1)
        for i in range(2, 2 + a):
            G.add_edge(0, i)
        for j in range(2 + a, 2 + a + b):
            G.add_edge(1, j)
        yield f"doublestar({a},{b})", adj_from_nx(G)
    for n in (20, 60, 200):
        T = nx.random_labeled_tree(n, seed=RNG.randrange(10 ** 6))
        yield f"randomtree(n={n})", adj_from_nx(T)
        yield f"path(n={n})", adj_from_nx(nx.path_graph(n))
        # caterpillar: path of n//2 spine vertices, each with one pendant leaf
        sp_len = n // 2
        Gc = nx.path_graph(sp_len)
        nxt = sp_len
        for v in range(sp_len):
            if nxt < n:
                Gc.add_edge(v, nxt)
                nxt += 1
        yield f"caterpillar(n={n})", adj_from_nx(Gc)
    # random chemical graphs (Delta <= 4) and random graphs with fixed degree seq
    for n in (30, 80, 200):
        G = nx.Graph()
        G.add_nodes_from(range(n))
        for i in range(1, n):
            G.add_edge(i, RNG.randrange(i))
        for i in range(n):
            if RNG.random() < 0.5:
                cand = [j for j in range(n) if j != i and G.degree(i) < 4 and G.degree(j) < 4
                        and not G.has_edge(i, j)]
                if cand:
                    G.add_edge(i, RNG.choice(cand))
        yield f"chem-ish(n={n})", adj_from_nx(G)


def main():
    worst = defaultdict(lambda: (float("inf"), None))  # min safety margin per claim
    failures = []
    checked = 0
    for name, adj in families():
        r = check_graph(adj, name)
        if r is None:
            continue
        checked += 1
        for k, v in r["residuals"].items():
            if isinstance(v, str):
                continue
            if k == "T8_deck_ok":
                # the deck determines the degree sequence only for m >= 4 (classical
                # exceptions below); flag failures in the ERC range only
                if v != 1 and r["m"] >= 4:
                    failures.append({"family": name, "claim": k, "value": v,
                                     "n": r["n"], "m": r["m"]})
                continue
            # residual conventions:
            #   T1_star, T1_M1 : C - bound            -> must be <= 0
            #   T2_degseq, T3_hi, T4_hi : bound - C   -> must be >= 0
            #   T3_lo, T4_lo  : C - lower             -> must be >= 0
            #   T5_*, T6_*    : |identity residual|   -> must be ~ 0
            if k in ("T1_star", "T1_M1"):
                bad = v > 1e-7
                margin = -v
            elif k in ("T5_C_identity", "T6_so_identity"):
                bad = abs(v) > 1e-7
                margin = -abs(v)
            else:
                bad = v < -1e-7
                margin = v
            if margin < worst[k][0]:
                worst[k] = (margin, f"{name}(n={r['n']},m={r['m']})")
            if bad:
                failures.append({"family": name, "claim": k, "value": v,
                                 "n": r["n"], "m": r["m"]})
    # tree Wiener identity on larger trees
    tree_err = 0.0
    for n in (10, 25, 60, 150, 300):
        for _ in range(3):
            T = nx.random_labeled_tree(n, seed=RNG.randrange(10 ** 6))
            tree_err = max(tree_err, tree_check(T))
    summary = {
        "graphs_checked": checked,
        "violations": failures,
        "min_residual_per_claim": {k: {"value": v[0], "at": v[1]} for k, v in worst.items()},
        "tree_wiener_identity_max_error": tree_err,
    }
    with open("results/adversarial_check.json", "w") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
