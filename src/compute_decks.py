"""
compute_decks.py -- build the edge deck (or vertex deck) of every graph and the
signature of every invariant over that deck.

Pipeline
  A. read the graph dataset (results/graphs.jsonl.gz);
  B. collect the *distinct* cards G-e (resp. G-v) over the whole dataset and
     fingerprint each of them exactly once -- there are at most a few thousand
     distinct cards per order, so this is dramatically cheaper than
     fingerprinting 5 million cards;
  C. fork worker processes that inherit the fingerprint table read-only and
     assemble, for every graph, the deck and one signature per invariant.

A signature of invariant I over the edge deck of G is the *sorted multiset*
    S_I(G) = sort { I(G-e) : e in E(G) }
which is exactly what an unlabelled deck can deliver.  The deck itself is
stored as the sorted multiset of card certificates (so deck collisions can be
detected and checked exactly).

Output (one gzip-compressed JSON object per line):
  i    graph6 of G                    n, m   order / size
  ce   certificate hex of G           ds     degree sequence
  fl   flag bitmask (see FLAGS)        dk     sorted card certificates (16 hex prefix of the full certificate)
  sig  "|"-joined signature hashes of the deck, in INVARIANTS order
  gsig "|"-joined hashes of the invariants of G itself
  so   quantised SO(G)                 sod    sorted quantised {SO(G-e)}
  dd   sorted quantised {SO(G)-SO(G-e)}          et  edge degree-type multiset
  dec  quantised values of a few structural invariants of G
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import multiprocessing as mp
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import graphlib as gl
import invariants as inv

# NOTE: the graph-set flags live in dataset.py (FLAG_CONNECTED = 1,
# FLAG_CHEMICAL = 64, FLAG_MGE4 = 256, ...).  This file used to redefine a
# second, conflicting set of FLAG_* constants that nothing here used; they were
# removed so that the two bit assignments cannot be confused.

DEC_KEYS = ["taus", "tri", "clique", "chrom", "indep", "wiener", "diam",
            "girth", "max_match", "n_perfect_match", "n_cut", "n_bridges",
            "energy", "spectral_radius", "m1", "m2", "randic", "abc",
            "sombor_inv", "sombor_sq", "adj_charpoly", "lap_charpoly", "adj_spec",
            "lap_spec", "q_spec", "dist_dist", "comp_sizes", "edge_types"]


def h8(obj) -> str:
    return hashlib.blake2b(repr(obj).encode(), digest_size=8).hexdigest()


def cards_of(adj, kind="edge"):
    """All cards of ``adj``: edge deletions G-e or vertex deletions G-v."""
    n = len(adj)
    out = []
    if kind == "edge":
        for u, v in gl.edges_of(adj):
            c = list(adj)
            c[u] &= ~(1 << v)
            c[v] &= ~(1 << u)
            out.append(tuple(c))
    else:
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
            out.append(tuple(c))
    return out


# --------------------------------------------------------------------------
def collect_distinct_cards(graphs, kind):
    table: dict[bytes, tuple[int, ...]] = {}
    for adj in graphs:
        for c in cards_of(adj, kind):
            cert = gl.canon_cert(c)
            if cert not in table:
                table[cert] = c
    return table


_FP_TABLE: dict[bytes, dict] = {}
_KIND = "edge"


def _worker_init(fp_table, kind):
    global _FP_TABLE, _KIND
    _FP_TABLE = fp_table
    _KIND = kind


def _process_graph(adj):
    """Assemble the record of one graph (runs in a worker process)."""
    n = len(adj)
    m = gl.n_edges(adj)
    gfp = inv.quantised_fingerprint(adj)
    cards = cards_of(adj, _KIND)
    certs = [gl.canon_cert(c) for c in cards]
    fps = [_FP_TABLE[c] for c in certs]
    inv_hashes = []
    for name in inv.INVARIANTS:
        vals = [fp[name] for fp in fps]
        vals.sort()
        inv_hashes.append(h8(vals))
    g_hashes = [h8(gfp[name]) for name in inv.INVARIANTS]
    so_q = gfp["sombor"]
    sod = sorted(fp["sombor"] for fp in fps)
    dd = sorted(so_q - x for x in sod)
    et = sorted(
        "%d-%d" % (min(gl.popcount(adj[u]), gl.popcount(adj[v])),
                   max(gl.popcount(adj[u]), gl.popcount(adj[v])))
        for u, v in gl.edges_of(adj)
    )
    dec = [gfp[k] for k in DEC_KEYS]
    g6 = gl.to_graph6(adj)
    return {
        "i": g6,
        "n": n,
        "m": m,
        "ce": gl.canon_cert(adj).hex(),
        "ds": ",".join(str(d) for d in gfp["deg_seq"]),
        "dk": ",".join(c.hex() for c in sorted(certs)),
        "sig": "|".join(inv_hashes),
        "gsig": "|".join(g_hashes),
        "so": so_q,
        "sod": ",".join(str(x) for x in sod),
        "dd": ",".join(str(x) for x in dd),
        "et": ",".join(et),
        "dec": dec,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graphs", default="results/graphs.jsonl.gz")
    ap.add_argument("--out", default="results/deck_edge.jsonl.gz")
    ap.add_argument("--kind", choices=["edge", "vertex"], default="edge")
    ap.add_argument("--workers", type=int, default=max(1, os.cpu_count() - 2))
    ap.add_argument("--chunksize", type=int, default=64)
    args = ap.parse_args()

    t0 = time.time()
    graphs = []
    with gzip.open(args.graphs, "rt") as f:
        for line in f:
            r = json.loads(line)
            graphs.append(gl.from_graph6(r["g6"]))
    print(f"[{time.time()-t0:6.1f}s] loaded {len(graphs)} graphs", flush=True)

    table = collect_distinct_cards(graphs, args.kind)
    print(f"[{time.time()-t0:6.1f}s] {len(table)} distinct {args.kind}-cards", flush=True)

    certs = list(table.keys())
    adjs = [table[c] for c in certs]
    fp_table: dict[bytes, dict] = {}
    with mp.Pool(args.workers) as pool:
        for cert, fp in zip(certs, pool.imap(inv.quantised_fingerprint, adjs, chunksize=16)):
            fp_table[cert] = fp
    print(f"[{time.time()-t0:6.1f}s] fingerprinted all distinct cards", flush=True)

    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    n_done = 0
    with mp.Pool(args.workers, initializer=_worker_init, initargs=(fp_table, args.kind)) as pool:
        with gzip.open(args.out, "wt", compresslevel=6) as out:
            for rec in pool.imap(_process_graph, graphs, chunksize=args.chunksize):
                out.write(json.dumps(rec, separators=(",", ":")) + "\n")
                n_done += 1
                if n_done % 20000 == 0:
                    print(f"[{time.time()-t0:6.1f}s] {n_done}/{len(graphs)}", flush=True)
    print(f"[{time.time()-t0:6.1f}s] wrote {args.out} ({n_done} records)", flush=True)


if __name__ == "__main__":
    main()
