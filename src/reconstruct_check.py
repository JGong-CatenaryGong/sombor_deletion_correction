"""
reconstruct_check.py -- independent, exact deck-collision check.

This is deliberately written as a *separate* implementation from
compute_decks.py / analyze_collisions.py so that the headline reconstructibility
statement does not rest on the main pipeline:

  * the deck of G is the sorted tuple of FULL nauty certificates of the cards
    (never a truncated certificate: truncation is canonical but not injective);
  * graphs are grouped by the deck itself, without any hashing;
  * every reported collision is verified twice -- by comparing the certificate
    tuples and by checking with networkx that the two graphs are not isomorphic.

Vertex decks are handled as well (card = G - v), which gives the analogous
statement for the vertex reconstruction conjecture.

Output: results/reconstruction_check.json
"""

from __future__ import annotations

import argparse
import gzip
import json
import multiprocessing as mp
import os
import sys
import time
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import networkx as nx
import graphlib as gl

FLAG_CONNECTED = 1
FLAG_MGE4 = 256


def decks_of(g6: str):
    adj = gl.from_graph6(g6)
    n = len(adj)
    geom = []
    for u, v in gl.edges_of(adj):
        c = list(adj)
        c[u] &= ~(1 << v)
        c[v] &= ~(1 << u)
        geom.append(gl.canon_cert(tuple(c)))
    vert = []
    for v in range(n):
        keep = [i for i in range(n) if i != v]
        idx = {old: new for new, old in enumerate(keep)}
        c = [0] * (n - 1)
        for i in keep:
            m = adj[i] & ~(1 << v)
            acc = 0
            while m:
                b = m & -m
                j = b.bit_length() - 1
                m ^= b
                acc |= 1 << idx[j]
            c[idx[i]] = acc
        vert.append(gl.canon_cert(tuple(c)))
    return tuple(sorted(geom)), tuple(sorted(vert))


def _work(g6):
    e, v = decks_of(g6)
    return g6, e, v


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graphs", default="results/graphs.jsonl.gz")
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 4) - 2))
    args = ap.parse_args()

    t0 = time.time()
    recs = []
    with gzip.open(args.graphs, "rt") as f:
        for line in f:
            recs.append(json.loads(line))
    print(f"loaded {len(recs)} graphs", flush=True)

    edge_groups = defaultdict(list)
    vert_groups = defaultdict(list)
    deck_key = {}   # graph6 -> (edge deck key, vertex deck key)
    with mp.Pool(args.workers) as pool:
        for i, (g6, e, v) in enumerate(pool.imap(_work, [r["g6"] for r in recs], chunksize=256)):
            edge_groups[e].append(g6)
            vert_groups[v].append(g6)
            deck_key[g6] = (e, v)
            if (i + 1) % 100000 == 0:
                print(f"  {i+1}/{len(recs)}", flush=True)
    print(f"[{time.time()-t0:.1f}s] decks computed", flush=True)

    meta = {r["g6"]: r for r in recs}
    out = {"n_graphs": len(recs), "hashing": "none (full certificates)", "decks": {}}
    for kind, groups in [("edge", edge_groups), ("vertex", vert_groups)]:
        colliding = {k: v for k, v in groups.items() if len(v) > 1}
        # verify with networkx that members of a colliding group are pairwise
        # non-isomorphic (a same-graph duplicate would be an implementation bug)
        verified = []
        for k, members in colliding.items():
            Gs = []
            for g6 in members:
                adj = gl.from_graph6(g6)
                G = nx.Graph()
                G.add_nodes_from(range(len(adj)))
                G.add_edges_from(gl.edges_of(adj))
                Gs.append(G)
            pairwise_iso = False
            for i in range(len(Gs)):
                for j in range(i + 1, len(Gs)):
                    if nx.is_isomorphic(Gs[i], Gs[j]):
                        pairwise_iso = True
            verified.append({
                "members": members,
                "n": [meta[g]["n"] for g in members],
                "m": [meta[g]["m"] for g in members],
                "found_isomorphic_pair": pairwise_iso,
                "flags": [meta[g]["fl"] for g in members],
            })
        # the same statement restricted to the range of the conjectures
        res = {}
        for label, test in [
            ("all", lambda r: True),
            ("m>=4", lambda r: r["fl"] & FLAG_MGE4),
            ("connected m>=4", lambda r: (r["fl"] & FLAG_CONNECTED) and (r["fl"] & FLAG_MGE4)),
        ]:
            sub = [r["g6"] for r in recs if test(r)]
            idx = 0 if kind == "edge" else 1
            subkeys = defaultdict(list)
            for g in sub:
                subkeys[deck_key[g][idx]].append(g)
            ncoll = sum(1 for v in subkeys.values() if len(v) > 1)
            res[label] = {"n_graphs": len(sub), "n_collision_classes": ncoll}
        out["decks"][kind] = {
            "n_collision_classes": len(colliding),
            "n_graphs_in_collisions": sum(len(v) for v in colliding.values()),
            "restricted": res,
            "examples": sorted(verified, key=lambda d: (min(d["n"]), min(d["m"]))),
        }
        print(f"{kind} decks: {len(colliding)} colliding classes, "
              f"{sum(len(v) for v in colliding.values())} graphs involved", flush=True)
        for e in out["decks"][kind]["examples"][:4]:
            print("   example:", e["members"], "n=", e["n"], "m=", e["m"],
                  "isomorphic_pair_found=", e["found_isomorphic_pair"], flush=True)

    with open("results/reconstruction_check.json", "w") as f:
        json.dump(out, f, indent=1, default=str)
    print("wrote results/reconstruction_check.json")


if __name__ == "__main__":
    main()
