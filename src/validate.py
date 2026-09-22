"""
validate.py -- correctness harness for the whole pipeline.

Checks performed
  1. enumeration counts against the known number of connected graphs
     (OEIS A001349) and, for n <= 7, against networkx.graph_atlas_g();
  2. canonical labelling: invariance under random relabelling, and injectivity
     on non-isomorphic graphs;
  3. every implemented invariant against an independent implementation
     (networkx / sympy / brute force);
  4. the Sombor edge-deletion formula against brute force;
  5. graph6 round-trip.

Run:  python src/validate.py
"""

from __future__ import annotations

import itertools
import json
import math
import random
import sys
import time

import networkx as nx
import numpy as np
import sympy as sp

import graphlib as gl
import invariants as inv

# number of unlabelled simple graphs on n nodes, OEIS A000088
A000088 = {1: 1, 2: 2, 3: 4, 4: 11, 5: 34, 6: 156, 7: 1044, 8: 12346, 9: 274668}
# number of connected unlabelled simple graphs, OEIS A001349
A001349 = {1: 1, 2: 1, 3: 2, 4: 6, 5: 21, 6: 112, 7: 853, 8: 11117, 9: 261080}
# OEIS A121941: unlabelled connected simple graphs with all degrees <= 4
# ("chemical graphs" in the sense of this study)
A121941 = {1: 1, 2: 1, 3: 2, 4: 6, 5: 21, 6: 78, 7: 353, 8: 1929, 9: 12207}

RESULTS: list[tuple[str, bool, str]] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((name, bool(ok), detail))
    print(f"[{'OK ' if ok else 'FAIL'}] {name} {detail}")


def nx_from_adj(adj) -> nx.Graph:
    G = nx.Graph()
    G.add_nodes_from(range(len(adj)))
    G.add_edges_from(gl.edges_of(adj))
    return G


def adj_from_nx(G: nx.Graph) -> tuple[int, ...]:
    nodes = sorted(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    return gl.from_edges(len(nodes), [(idx[u], idx[v]) for u, v in G.edges()])


# --------------------------------------------------------------------------
def test_enumeration():
    print("\n== 1. enumeration counts ==")
    levels = gl.enumerate_graphs_by_order(9, maxdeg=None)
    for n in range(1, 10):
        got = len(levels[n])
        check(f"all graphs n={n} == A000088", got == A000088[n], f"{got} vs {A000088[n]}")
    for n in range(1, 10):
        got = sum(1 for a in levels[n].values() if gl.connected(a))
        check(f"connected graphs n={n} == A001349", got == A001349[n], f"{got} vs {A001349[n]}")
    for n in range(1, 10):
        got = sum(1 for a in levels[n].values() if gl.connected(a) and gl.max_degree(a) <= 4)
        check(f"chemical (conn, maxdeg<=4) n={n} == A121941", got == A121941[n], f"{got} vs {A121941[n]}")
    # independent re-enumeration directly constrained to max degree <= 4
    lev4 = gl.enumerate_graphs_by_order(9, maxdeg=4)
    for n in range(1, 10):
        got4 = sum(1 for a in lev4[n].values() if gl.connected(a))
        check(f"maxdeg<=4 enumerator agrees n={n}", got4 == A121941[n], f"{got4} vs {A121941[n]}")
    # cross-check with the graph atlas for n <= 7
    atlas = {n: set() for n in range(1, 8)}
    for G in nx.graph_atlas_g():
        n = G.number_of_nodes()
        if n == 0 or not nx.is_connected(G):
            continue
        adj = adj_from_nx(G)
        atlas[n].add(gl.canon_cert(adj))
    for n in range(1, 8):
        mine = {cert for cert, a in levels[n].items() if gl.connected(a)}
        check(
            f"atlas cross-check (connected) n={n}",
            mine == atlas[n],
            f"{len(mine)} vs {len(atlas[n])}",
        )
    return levels


def test_canonical(levels):
    print("\n== 2. canonical labelling ==")
    rng = random.Random(20240517)
    bad_perm = 0
    for n in range(4, 9):
        sample = list(levels[n].values())
        rng.shuffle(sample)
        for adj in sample[:60]:
            for _ in range(3):
                p = list(range(n))
                rng.shuffle(p)
                if gl.canon_cert(gl.permute(adj, p)) != gl.canon_cert(adj):
                    bad_perm += 1
    check("certificate invariant under relabelling", bad_perm == 0, f"{bad_perm} failures")

    # injectivity: distinct certificates must mean non-isomorphic
    clashes = 0
    for n in range(4, 9):
        sample = list(levels[n].values())
        rng.shuffle(sample)
        for a, b in itertools.combinations(sample[:120], 2):
            if gl.canon_cert(a) == gl.canon_cert(b):
                if not nx.is_isomorphic(nx_from_adj(a), nx_from_adj(b)):
                    clashes += 1
    check("distinct certificates => non-isomorphic", clashes == 0, f"{clashes} clashes")

    # graph6 round trip
    bad6 = 0
    for n in range(2, 9):
        for adj in list(levels[n].values())[:200]:
            if gl.from_graph6(gl.to_graph6(adj)) != adj:
                bad6 += 1
    check("graph6 round-trip", bad6 == 0, f"{bad6} failures")


def test_invariants(levels):
    print("\n== 3. invariants vs independent implementations ==")
    rng = random.Random(7)
    pool = []
    for n in range(3, 10):                     # n = 9 is sampled as well (P22)
        s = list(levels[n].values())
        rng.shuffle(s)
        pool.extend(s[:40])
    bad = {k: 0 for k in
           ["so", "so_inv", "so_sq", "so_red", "randic", "abc", "m1", "m2", "forgotten",
            "harmonic", "ga", "sum_conn", "isi", "az", "wiener", "taus", "tri",
            "clique", "indep", "chrom", "match", "n_perfect_match", "max_match",
            "adj_spec", "lap_spec", "q_spec", "charpoly", "lap_charpoly",
            "energy", "spectral_radius",
            "girth", "diam", "ecc_seq", "dist_dist", "bridges", "bip", "deg",
            "n", "m", "n_comp", "comp_sizes", "max_deg", "min_deg", "n_leaves",
            "n_cut", "forest", "biconnected", "edge_types"]}
    for adj in pool:
        G = nx_from_adj(adj)
        d = dict(G.degree())
        fp = inv.fingerprint(adj)
        if abs(inv.sombor(adj) - sum(math.sqrt(d[u] ** 2 + d[v] ** 2) for u, v in G.edges())) > 1e-12:
            bad["so"] += 1
        if abs(inv.sombor_inverse(adj) - sum(1 / math.sqrt(d[u] ** 2 + d[v] ** 2) for u, v in G.edges())) > 1e-12:
            bad["so_inv"] += 1
        if abs(inv.randic(adj) - sum(1 / math.sqrt(d[u] * d[v]) for u, v in G.edges())) > 1e-12:
            bad["randic"] += 1
        if abs(inv.abc(adj) - sum(math.sqrt((d[u] + d[v] - 2) / (d[u] * d[v])) for u, v in G.edges())) > 1e-12:
            bad["abc"] += 1
        if inv.zagreb_m1(adj) != sum(v * v for v in d.values()):
            bad["m1"] += 1
        if inv.zagreb_m2(adj) != sum(d[u] * d[v] for u, v in G.edges()):
            bad["m2"] += 1
        # our Wiener index is the generalised one; networkx reports inf when the
        # graph is disconnected, so only connected graphs are comparable
        if nx.is_connected(G) and inv.distance_profile(adj)[1] != nx.wiener_index(G):
            bad["wiener"] += 1
        elif not nx.is_connected(G):
            comps = list(nx.connected_components(G))
            ref = 0
            for c in comps:
                ref += nx.wiener_index(G.subgraph(c))
            if inv.distance_profile(adj)[1] != ref:
                bad["wiener"] += 1
        # networkx returns a float determinant: compare with tolerance
        if abs(inv.n_spanning_trees(adj) - float(nx.number_of_spanning_trees(G))) > 1e-6:
            bad["taus"] += 1
        tri_nx = sum(nx.triangles(G).values()) // 3
        if inv.fingerprint(adj)["tri"] != tri_nx:
            bad["tri"] += 1
        # independent brute-force clique / independence (all vertex subsets)
        nn = len(adj)
        best_c = 0
        best_i = 0
        for mask in range(1 << nn):
            vs = [v for v in range(nn) if mask >> v & 1]
            pairs = list(itertools.combinations(vs, 2))
            if all((adj[u] >> v) & 1 for u, v in pairs):
                best_c = max(best_c, len(vs))
            if not any((adj[u] >> v) & 1 for u, v in pairs):
                best_i = max(best_i, len(vs))
        if inv.clique_number(adj) != best_c:
            bad["clique"] += 1
        if inv.independence_number(adj) != best_i:
            bad["indep"] += 1
        # chromatic: brute force over colourings for n <= 6
        if len(adj) <= 6:
            n = len(adj)
            brute = None
            for k in range(1, n + 1):
                for col in itertools.product(range(k), repeat=n):
                    if all(col[u] != col[v] for u, v in G.edges()):
                        brute = k
                        break
                if brute:
                    break
            if inv.chromatic_number(adj) != brute:
                bad["chrom"] += 1
        # matching polynomial: brute force over edge subsets
        E = list(G.edges())
        cnt = [0] * (len(adj) // 2 + 1)
        for r in range(0, min(len(E), len(adj) // 2) + 1):
            for sub in itertools.combinations(E, r):
                vs = set()
                ok = True
                for u, v in sub:
                    if u in vs or v in vs:
                        ok = False
                        break
                    vs.add(u)
                    vs.add(v)
                if ok:
                    cnt[r] += 1
        mine_mp = inv.matching_counts(adj)
        # ours is truncated at the matching number; the reference is zero-padded
        if mine_mp != tuple(cnt[: len(mine_mp)]):
            bad["match"] += 1
        if not np.allclose(np.sort(inv.adj_spectrum(adj)), np.sort(nx.adjacency_spectrum(G)), atol=1e-9):
            bad["adj_spec"] += 1
        if not np.allclose(np.sort(inv.lap_spectrum(adj)), np.sort(nx.laplacian_spectrum(G)), atol=1e-9):
            bad["lap_spec"] += 1
        # charpoly vs sympy (exact)
        x = sp.symbols("x")
        A = sp.Matrix(nx.to_numpy_array(G, nodelist=sorted(G.nodes())).astype(int).tolist())
        exact = sp.Poly(A.charpoly(x).as_expr(), x).all_coeffs()
        if tuple(int(c) for c in exact) != inv.charpoly_coeffs(adj):
            bad["charpoly"] += 1
        mcb = nx.minimum_cycle_basis(G)
        g_ref = len(min(mcb, key=len)) if mcb else 0
        if inv.girth(adj) != g_ref:
            bad["girth"] += 1
        if len(adj) <= 8 and nx.is_connected(G):
            if inv.diameter(adj) != nx.diameter(G):
                bad["diam"] += 1
        if gl.n_bridges(adj) != len(list(nx.bridges(G))):
            bad["bridges"] += 1
        if gl.bipartite(adj) != int(nx.is_bipartite(G)):
            bad["bip"] += 1
        if inv.degree_sequence(adj) != tuple(sorted((v for _, v in G.degree()), reverse=True)):
            bad["deg"] += 1
        # ---- size / structure ------------------------------------------------
        dd = sorted((v for _, v in G.degree()), reverse=True)
        if gl.n_vertices(adj) != G.number_of_nodes():
            bad["n"] += 1
        if gl.n_edges(adj) != G.number_of_edges():
            bad["m"] += 1
        if gl.n_components(adj) != nx.number_connected_components(G):
            bad["n_comp"] += 1
        comp_ref = tuple(sorted((len(c) for c in nx.connected_components(G)), reverse=True))
        if inv.component_sizes(adj) != comp_ref:
            bad["comp_sizes"] += 1
        if gl.max_degree(adj) != max(dd):
            bad["max_deg"] += 1
        if inv.fingerprint(adj)["min_deg"] != min(dd):
            bad["min_deg"] += 1
        if inv.fingerprint(adj)["n_leaves"] != sum(1 for x in dd if x == 1):
            bad["n_leaves"] += 1
        if inv.n_cut_vertices(adj) != len(list(nx.articulation_points(G))):
            bad["n_cut"] += 1
        if gl.is_forest(adj) != int(nx.is_forest(G)):
            bad["forest"] += 1
        if len(adj) >= 3 and nx.is_connected(G):
            if inv.fingerprint(adj)["biconnected"] != int(nx.is_biconnected(G)):
                bad["biconnected"] += 1
        et_ref = tuple(sorted(tuple(sorted((d[u], d[v]))) for u, v in G.edges()))
        if fp["edge_types"] != et_ref:
            bad["edge_types"] += 1
        # ---- eccentricities / distance distribution (connected only) ---------
        if nx.is_connected(G):
            if tuple(inv.distance_profile(adj)[3]) != tuple(
                    sorted(nx.eccentricity(G).values(), reverse=True)):
                bad["ecc_seq"] += 1
            spl = dict(nx.all_pairs_shortest_path_length(G))
            hist = [0] * (len(adj))
            for u in spl:
                for w2, dist in spl[u].items():
                    if dist:
                        hist[dist] += 1
            hist = [c // 2 for c in hist]          # ordered -> unordered pairs
            if tuple(inv.distance_profile(adj)[0]) != tuple(h for h in hist[1:] if h):
                bad["dist_dist"] += 1
        # ---- matchings --------------------------------------------------------
        if fp["max_match"] != len(nx.max_weight_matching(G, maxcardinality=True)):
            bad["max_match"] += 1
        if len(adj) % 2 == 0:
            if fp["n_perfect_match"] != cnt[len(adj) // 2]:
                bad["n_perfect_match"] += 1
        # ---- remaining degree-based indices (direct formulas) -----------------
        pairs = [(d[u], d[v]) for u, v in G.edges()]
        if abs(inv.sombor_squared(adj) - sum(a * a + b * b for a, b in pairs)) > 1e-12:
            bad["so_sq"] += 1
        if abs(inv.sombor_reduced(adj) - sum(math.hypot(a - 1, b - 1) for a, b in pairs)) > 1e-12:
            bad["so_red"] += 1
        if inv.forgotten(adj) != sum(v ** 3 for v in dd):
            bad["forgotten"] += 1
        if abs(inv.harmonic(adj) - sum(2 / (a + b) for a, b in pairs)) > 1e-12:
            bad["harmonic"] += 1
        if abs(inv.geometric_arithmetic(adj)
               - sum(2 * math.sqrt(a * b) / (a + b) for a, b in pairs)) > 1e-12:
            bad["ga"] += 1
        if abs(inv.sum_connectivity(adj) - sum(1 / math.sqrt(a + b) for a, b in pairs)) > 1e-12:
            bad["sum_conn"] += 1
        if abs(inv.inverse_sum_indeg(adj) - sum(a * b / (a + b) for a, b in pairs)) > 1e-12:
            bad["isi"] += 1
        if abs(inv.augmented_zagreb(adj)
               - sum((a * b / (a + b - 2)) ** 3 for a, b in pairs if a + b > 2)) > 1e-12:
            bad["az"] += 1
        # ---- spectra / polynomials / energy ----------------------------------
        A_np = nx.to_numpy_array(G, nodelist=sorted(G.nodes()))
        D_np = np.diag(A_np.sum(axis=1))
        if not np.allclose(np.sort(np.linalg.eigvalsh(D_np + A_np)),
                           np.sort(inv.signless_lap_spectrum(adj)), atol=1e-9):
            bad["q_spec"] += 1
        L_int = (D_np - A_np).astype(int)
        exact_lap = sp.Poly(sp.Matrix(L_int.tolist()).charpoly(x).as_expr(), x).all_coeffs()
        if tuple(int(c) for c in exact_lap) != inv.lap_charpoly_coeffs(adj):
            bad["lap_charpoly"] += 1
        ev = np.linalg.eigvalsh(A_np)
        if abs(fp["energy"] - float(np.sum(np.abs(ev)))) > 1e-9:
            bad["energy"] += 1
        if abs(fp["spectral_radius"] - float(max(ev) if len(ev) else 0.0)) > 1e-9:
            bad["spectral_radius"] += 1
    for k, v in bad.items():
        check(f"invariant '{k}' matches reference", v == 0, f"{v} mismatches")


def test_sombor_formula(levels):
    """Delta_e = SO(G) - SO(G-e) against the closed formula."""
    print("\n== 4. Sombor edge-deletion formula ==")
    rng = random.Random(11)
    worst = 0.0
    worst_id = None
    for n in range(2, 9):
        s = list(levels[n].values())
        rng.shuffle(s)
        for adj in s[:80]:
            deg = gl.degrees(adj)
            so = inv.sombor(adj)
            for u, v in gl.edges_of(adj):
                a, b = deg[u], deg[v]
                # brute force
                card = list(adj)
                card[u] &= ~(1 << v)
                card[v] &= ~(1 << u)
                delta_bf = so - inv.sombor(tuple(card))
                # closed formula
                term = math.sqrt(a * a + b * b)
                mu = adj[u] & ~(1 << v)
                while mu:
                    bb = mu & -mu
                    x = bb.bit_length() - 1
                    mu ^= bb
                    dx = deg[x]
                    term += math.sqrt(a * a + dx * dx) - math.sqrt((a - 1) ** 2 + dx * dx)
                mv = adj[v] & ~(1 << u)
                while mv:
                    bb = mv & -mv
                    y = bb.bit_length() - 1
                    mv ^= bb
                    dy = deg[y]
                    term += math.sqrt(b * b + dy * dy) - math.sqrt((b - 1) ** 2 + dy * dy)
                e = abs(term - delta_bf)
                if e > worst:
                    worst = e
                    worst_id = (n, gl.to_graph6(adj), (u, v))
    check("Delta_e closed formula == brute force", worst < 1e-9, f"max err {worst:.3e} at {worst_id}")

    # corrected summation identity
    worst2 = 0.0
    for n in range(2, 9):
        s = list(levels[n].values())
        rng.shuffle(s)
        for adj in s[:80]:
            deg = gl.degrees(adj)
            so = inv.sombor(adj)
            m = gl.n_edges(adj)
            lhs = 0.0
            for u, v in gl.edges_of(adj):
                card = list(adj)
                card[u] &= ~(1 << v)
                card[v] &= ~(1 << u)
                lhs += inv.sombor(tuple(card))
            corr = 0.0
            for u in range(n):
                a = deg[u]
                mu = adj[u]
                while mu:
                    bb = mu & -mu
                    x = bb.bit_length() - 1
                    mu ^= bb
                    dx = deg[x]
                    corr += (a - 1) * (math.sqrt(a * a + dx * dx) - math.sqrt((a - 1) ** 2 + dx * dx))
            rhs = (m - 1) * so - corr
            worst2 = max(worst2, abs(lhs - rhs))
    check("sum_e SO(G-e) == (m-1)SO(G) - correction", worst2 < 1e-9, f"max err {worst2:.3e}")


def test_performance(levels):
    print("\n== 5. performance ==")
    rng = random.Random(3)
    s = list(levels[8].values())
    rng.shuffle(s)
    t0 = time.perf_counter()
    N = 300
    for adj in s[:N]:
        inv.fingerprint(adj)
    dt = (time.perf_counter() - t0) / N
    print(f"fingerprint(n=8): {dt*1e6:.0f} us/graph")
    t0 = time.perf_counter()
    for adj in s[:N]:
        for u, v in gl.edges_of(adj):
            c = list(adj)
            c[u] &= ~(1 << v)
            c[v] &= ~(1 << u)
            gl.canon_cert(tuple(c))
    print(f"deck certificates(n=8): {(time.perf_counter()-t0)/N*1e6:.0f} us/graph")


def main():
    t0 = time.time()
    levels = test_enumeration()
    test_canonical(levels)
    test_invariants(levels)
    test_sombor_formula(levels)
    test_performance(levels)
    nfail = sum(1 for _, ok, _ in RESULTS if not ok)
    print(f"\n==== {len(RESULTS)-nfail}/{len(RESULTS)} checks passed in {time.time()-t0:.1f}s ====")
    with open("results/validation.json", "w") as f:
        json.dump(
            {
                "checks": [{"name": n, "ok": ok, "detail": d} for n, ok, d in RESULTS],
                "n_failed": nfail,
                "seconds": time.time() - t0,
            },
            f,
            indent=1,
        )
    return 1 if nfail else 0


if __name__ == "__main__":
    sys.exit(main())
