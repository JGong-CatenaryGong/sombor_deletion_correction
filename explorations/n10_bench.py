"""
n10_bench.py -- measured cost model for pushing the pipeline from n<=9 to n=10.

Measures (all timings wall-clock, this machine):
  1. enumeration: all graphs n<=9 (calibration) and deg<=4 graphs n<=10 (chemical);
  2. chemical n=10 count (== A121941(10) = 89,402) and planar sub-count (CHEMP);
  3. per-graph invariant cost: invariants.fingerprint on samples at n=9 and n=10;
  4. canonical-certificate throughput (the deck bottleneck) at n=9/n=10;
  5. planarity-check cost (build_dataset flags).
Then extrapolates the full pipeline cost for the three tiers
   A: CHEM n=10 (deg<=4, connected)   B: CHEMP n=10 (+planar)   C: ALL n=10.
"""
import os
import sys
import time
import gzip
import json
import resource

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, ".pylibs"))
sys.path.insert(0, os.path.join(ROOT, "src"))
import graphlib as gl
import invariants as inv


def timed(label, fn):
    t = time.perf_counter()
    r = fn()
    dt = time.perf_counter() - t
    print(f"[{label}] {dt:.2f}s", flush=True)
    return r, dt


def main():
    # ---------- 1. enumeration ----------
    levels9, t9 = timed("enum n<=9 ALL", lambda: gl.enumerate_graphs_by_order(9))
    print("   levels:", [len(l) for l in levels9], "total", sum(len(l) for l in levels9), flush=True)
    lv10, t10 = timed("enum n<=10 maxdeg=4", lambda: gl.enumerate_graphs_by_order(10, maxdeg=4))
    print("   level10 (deg<=4, all):", len(lv10[10]), " cumulative:", sum(len(l) for l in lv10), flush=True)
    conn10, tc = timed("filter connected n=10",
                       lambda: [a for a in lv10[10].values() if gl.connected(a)])
    print("   CHEM n=10 (connected, deg<=4):", len(conn10), "(A121941(10)=89402)", flush=True)

    # ---------- 2. planarity cost on a sample ----------
    try:
        import networkx as nx
        samp = conn10[:300]
        t = time.perf_counter()
        for a in samp:
            G = nx.Graph()
            G.add_nodes_from(range(len(a)))
            G.add_edges_from(gl.edges_of(a))
            nx.check_planarity(G)
        tp = (time.perf_counter() - t) / len(samp)
        print(f"[planarity] {tp*1000:.2f} ms/graph  -> CHEM n=10: {tp*len(conn10):.0f}s", flush=True)
    except ImportError:
        tp = None
        print("[planarity] networkx missing", flush=True)

    # ---------- 3. per-graph invariant cost ----------
    gr9 = []
    with gzip.open(os.path.join(ROOT, "results", "graphs.jsonl.gz"), "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["n"] == 9 and (r["fl"] & 64):          # chemical n=9
                gr9.append(gl.from_graph6(r["g6"]))
            if len(gr9) >= 120:
                break
    t = time.perf_counter()
    for a in gr9:
        inv.fingerprint(a)
    tf9 = (time.perf_counter() - t) / len(gr9)
    print(f"[fingerprint n=9 chemical] {tf9*1000:.2f} ms/graph", flush=True)

    t = time.perf_counter()
    for a in conn10[:120]:
        inv.fingerprint(a)
    tf10 = (time.perf_counter() - t) / 120
    print(f"[fingerprint n=10 chemical] {tf10*1000:.2f} ms/graph", flush=True)

    # ---------- 4. certificate throughput (deck bottleneck) ----------
    t = time.perf_counter()
    for a in conn10[:200]:
        gl.canon_cert(a)
    tc10 = (time.perf_counter() - t) / 200
    print(f"[canon_cert n=10] {tc10*1000:.3f} ms/call", flush=True)
    t = time.perf_counter()
    for a in gr9[:200]:
        gl.canon_cert(a)
    tc9 = (time.perf_counter() - t) / 200
    print(f"[canon_cert n=9] {tc9*1000:.3f} ms/call", flush=True)

    m9 = sum(gl.n_edges(a) for a in gr9) / len(gr9)
    m10 = sum(gl.n_edges(a) for a in conn10[:200]) / 200
    print(f"[avg m] n=9 chemical {m9:.2f}, n=10 chemical {m10:.2f}", flush=True)

    # ---------- 5. extrapolation ----------
    ALL10 = 12_005_168
    chem10 = len(conn10)
    print("\n=== extrapolation (single-thread; pipeline uses 20-22 workers for decks) ===",
          flush=True)
    print(f"CHEM n=10 = {chem10:,} graphs:", flush=True)
    print(f"   build_dataset (flags incl. planarity): {tp*chem10:.0f}s" if tp else "", flush=True)
    print(f"   invariants (fingerprint x N): {tf10*chem10/60:.1f} min", flush=True)
    print(f"   deck cards: {m10*chem10/1e6:.2f}M canon calls "
          f"@ {tc10*1000:.2f} ms -> {m10*chem10*tc10/60:.1f} min "
          f"(/22 workers: {m10*chem10*tc10/22/60:.1f} min)", flush=True)
    print(f"   deck storage: ~{370775597*m10*chem10/(m9*1440):.0f} MB" if False else "", flush=True)
    print(f"ALL n=10 = {ALL10:,} graphs (x{ALL10/sum(len(l) for l in levels9):.1f} of n<=9):",
          flush=True)
    print(f"   enumeration measured above for maxdeg=4; ALL n=10 enumeration is run separately",
          flush=True)
    print(f"   invariants: {tf10*ALL10/3600:.1f} h single-thread", flush=True)
    print(f"   deck cards: {m10*ALL10/1e6:.0f}M canon calls -> {m10*ALL10*tc10/22/3600:.1f} h on 22 workers",
          flush=True)
    print(f"   deck jsonl.gz: ~{370775597*ALL10/288266/1024:.1f} GB (linear scaling of n<=9 file)",
          flush=True)
    print(f"peak RSS this process: {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1e6:.2f} GB",
          flush=True)


if __name__ == "__main__":
    main()
