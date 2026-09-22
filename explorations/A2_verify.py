"""
A2 -- verification of the tree Wiener aggregation identity

    (T)   sum_{e in E(T)} W(T - e)  =  m * W(T) - S2(T)  =  (m+1) * W(T) - 2 * WW(T),

where W is the generalized Wiener index (sum of distances over same-component
unordered pairs), S2(T) = sum_{z<w} d(z,w)^2, WW(T) = sum_{z<w} d(z,w)(d(z,w)+1)/2
is the hyper-Wiener index, and m = |E(T)| = n-1 for a tree.

Also verifies the bridge-aggregate formula for GENERAL graphs (every bridge
e = uv with sides A (u) and B (v) satisfies the exact per-edge formula of
report section 9.2; summing over bridges only):

    (B)   sum_{e bridge} [W(G) - W(G-e)]
            = sum_{z<w} b(z,w)
            + sum_{z != w (ordered)} sum_{e bridge separating z,w} d(z, proj_e(z)),

where b(z,w) = number of bridges separating z and w, and proj_e(z) is the
endpoint of e on z's side (so d(z,proj_e(z)) = min(d(z,u_e), d(z,v_e))).

For trees every edge is a bridge, b(z,w) = d(z,w) and the inner sum telescopes
to sum_k (k-1) = d(d-1)/2 per pair, giving (T).

Scope (all exact integer arithmetic, BFS distances):
  * ALL trees of the frozen n<=9 dataset (FLAG_TREE, read-only): exhaustive;
  * random labeled trees n = 20..150 (3 seeds each) + paths P_n (n=5..14,
    checking sum_e W(P_n-e) = 2*C(n+1,4)) + stars K_{1,k} (checking k(k-1)^2);
  * bridge formula (B): 400 sampled connected n<=9 dataset graphs having at
    least one bridge + random sparse G(n,p) n=14..24 connected with bridges.

Output: explorations/results/A2_verification.json
"""
import os
import sys
import gzip
import json
import math
import random
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "src"))
import graphlib as gl

import networkx as nx

FLAG_TREE = 32
FLAG_CONNECTED = 1


def nbrs(adj):
    n = len(adj)
    return [[j for j in range(n) if (adj[i] >> j) & 1] for i in range(n)]


def bfs_dists(nb, s):
    dist = {s: 0}
    dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in nb[u]:
            if w not in dist:
                dist[w] = dist[u] + 1
                dq.append(w)
    return dist


def all_dists(adj):
    nb = nbrs(adj)
    return [bfs_dists(nb, s) for s in range(len(adj))]


def W_S2_WW_from_dists(dists):
    n = len(dists)
    W = S2 = WW = 0
    for z in range(n):
        for w in range(z + 1, n):
            d = dists[z].get(w)
            if d is None:
                continue
            W += d
            S2 += d * d
            WW += d * (d + 1) // 2
    return W, S2, WW


def delete_edge(adj, u, v):
    c = list(adj)
    c[u] &= ~(1 << v)
    c[v] &= ~(1 << u)
    return tuple(c)


def check_tree(adj):
    """Verify (T) exhaustively for one tree; returns max abs error (int)."""
    dists = all_dists(adj)
    W, S2, WW = W_S2_WW_from_dists(dists)
    m = gl.n_edges(adj)
    lhs = 0
    for u, v in gl.edges_of(adj):
        cw, _, _ = W_S2_WW_from_dists(all_dists(delete_edge(adj, u, v)))
        lhs += cw
    e1 = lhs - (m * W - S2)
    e2 = lhs - ((m + 1) * W - 2 * WW)
    return max(abs(e1), abs(e2)), {"m": m, "W": W, "S2": S2, "WW": WW, "sum_cards": lhs}


def bridges_of(adj):
    G = nx.Graph()
    G.add_nodes_from(range(len(adj)))
    G.add_edges_from(gl.edges_of(adj))
    return list(nx.bridges(G))


def check_bridge_formula(adj):
    """Verify (B) for a general graph (exact integers)."""
    brs = [(u, v) for u, v in bridges_of(adj)]
    if not brs:
        return None
    dists = all_dists(adj)
    W, _, _ = W_S2_WW_from_dists(dists)
    n = len(adj)
    # LHS: sum over bridges of W(G) - W(G-e)
    lhs = 0
    for u, v in brs:
        cw, _, _ = W_S2_WW_from_dists(all_dists(delete_edge(adj, u, v)))
        lhs += W - cw
    # RHS via pairs: b(z,w) + sum over separating bridges of
    # d(z, proj_e(z)) + d(w, proj_e(w))  (unordered pairs {z,w})
    sides = []
    for u, v in brs:
        du = bfs_dists(nbrs(delete_edge(adj, u, v)), u)
        sides.append(set(du))            # A-side (u's component)
    rhs = 0
    for z in range(n):
        for w in range(z + 1, n):
            if dists[z].get(w) is None:
                continue                 # different components already in G
            for (u, v), A in zip(brs, sides):
                if (z in A) == (w in A):
                    continue             # not separated by this bridge
                rhs += 1                 # b(z,w) term
                rhs += (dists[z][u] if z in A else dists[z][v])
                rhs += (dists[w][v] if z in A else dists[w][u])
    return abs(lhs - rhs), {"n_bridges": len(brs), "lhs": lhs, "rhs": rhs}


def main():
    out = {"script": "explorations/A2_verify.py"}

    # ---- (1) all dataset trees n <= 9 -------------------------------------
    trees = []
    conn = []
    with gzip.open(os.path.join(ROOT, "results", "graphs.jsonl.gz"), "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["fl"] & FLAG_TREE:
                trees.append(r["g6"])
            elif (r["fl"] & FLAG_CONNECTED) and r["m"] >= 2:
                conn.append(r["g6"])
    err = 0
    worst = None
    for g6 in trees:
        e, info = check_tree(gl.from_graph6(g6))
        if e > err:
            err, worst = e, (g6, info)
    out["dataset_trees"] = {"n_checked": len(trees), "max_error": err,
                            "worst": worst[0] if worst else None}
    print(f"dataset trees: {len(trees)} checked, max error {err}", flush=True)

    # ---- (2) large random trees, paths, stars ------------------------------
    rng = random.Random(20260921)
    big_err = 0
    big_n = 0
    for n in (20, 50, 100, 150):
        for seed in (1, 2, 3):
            T = nx.random_labeled_tree(n, seed=seed * 1000 + n)
            adj = gl.from_edges(n, [(u, v) for u, v in T.edges()])
            e, _ = check_tree(adj)
            big_err = max(big_err, e)
            big_n += 1
    # paths: sum_e W(P_n - e) = 2*C(n+1,4)
    path_err = 0
    for n in range(5, 15):
        adj = gl.from_edges(n, [(i, i + 1) for i in range(n - 1)])
        dists = all_dists(adj)
        W, S2, _ = W_S2_WW_from_dists(dists)
        m = n - 1
        lhs = sum(W_S2_WW_from_dists(all_dists(delete_edge(adj, u, v)))[0]
                  for u, v in gl.edges_of(adj))
        closed = 2 * math.comb(n + 1, 4)
        path_err = max(path_err, abs(lhs - (m * W - S2)), abs(lhs - closed))
    # stars: sum_e W(K_{1,k} - e) = k(k-1)^2
    star_err = 0
    for k in range(2, 13):
        n = k + 1
        adj = gl.from_edges(n, [(0, i) for i in range(1, n)])
        dists = all_dists(adj)
        W, S2, _ = W_S2_WW_from_dists(dists)
        lhs = sum(W_S2_WW_from_dists(all_dists(delete_edge(adj, u, v)))[0]
                  for u, v in gl.edges_of(adj))
        star_err = max(star_err, abs(lhs - (k * W - S2)), abs(lhs - k * (k - 1) ** 2))
    out["large_trees"] = {"n_checked": big_n, "max_error": big_err}
    out["paths"] = {"n_range": [5, 14], "max_error_incl_closed_form": path_err}
    out["stars"] = {"k_range": [2, 12], "max_error_incl_closed_form": star_err}
    print(f"large trees {big_n} err {big_err}; paths err {path_err}; stars err {star_err}",
          flush=True)

    # ---- (3) bridge formula on general graphs ------------------------------
    br_err = 0
    br_n = 0
    sample = rng.sample(conn, 400)
    for g6 in sample:
        adj = gl.from_graph6(g6)
        res = check_bridge_formula(adj)
        if res is None:
            continue
        br_n += 1
        br_err = max(br_err, res[0])
    # random sparse graphs (larger, with bridges)
    for n, p in ((14, 0.15), (18, 0.12), (24, 0.08)):
        for seed in range(6):
            G = nx.gnp_random_graph(n, p, seed=seed * 77 + n)
            if not nx.is_connected(G) or not list(nx.bridges(G)):
                continue
            adj = gl.from_edges(n, [(u, v) for u, v in G.edges()])
            res = check_bridge_formula(adj)
            if res:
                br_n += 1
                br_err = max(br_err, res[0])
    out["bridge_formula"] = {"n_checked": br_n, "max_error": br_err}
    print(f"bridge formula: {br_n} graphs, max error {br_err}", flush=True)

    out["identities"] = {
        "tree": "sum_e W(T-e) = m*W(T) - S2(T) = (m+1)*W(T) - 2*WW(T)",
        "path_corollary": "sum_e W(P_n-e) = 2*C(n+1,4)",
        "star_corollary": "sum_e W(K_{1,k}-e) = k*(k-1)^2",
        "bridge_general": "sum_{e bridge} [W(G)-W(G-e)] = sum_{z<w} b(z,w) + sum_{ordered z!=w} sum_{e sep} d(z,proj_e(z))",
    }
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    with open(os.path.join(HERE, "results", "A2_verification.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
