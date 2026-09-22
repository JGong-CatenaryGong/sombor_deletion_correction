"""Full ALL n=10 enumeration benchmark: count + wall time + peak RSS.
Leaner than graphlib's version: only certificate sets are kept per level."""
import sys, os, time, itertools, resource
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, ".pylibs")); sys.path.insert(0, os.path.join(ROOT, "src"))
import graphlib as gl

t0 = time.perf_counter()
cur = {gl.canon_cert(gl.empty_graph(1)): gl.empty_graph(1)}
counts = [0, 1]
for k in range(1, 10):
    nxt = {}
    for cert, adj in cur.items():
        for r in range(0, k + 1):
            for comb in itertools.combinations(range(k), r):
                newadj = list(adj) + [0]; m = 0
                for i in comb:
                    m |= 1 << i; newadj[i] |= 1 << k
                newadj[k] = m
                c = gl.canon_cert(tuple(newadj))
                if c not in nxt:
                    nxt[c] = tuple(newadj)
    cur = nxt
    counts.append(len(cur))
    print(f"  level {k+1}: {len(cur):,} graphs  [{time.perf_counter()-t0:.1f}s, "
          f"RSS {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1e6:.2f} GB]", flush=True)
print("counts:", counts)
print("total:", sum(counts))
print(f"ALL n<=10 enumeration: {time.perf_counter()-t0:.1f}s "
      f"({(time.perf_counter()-t0)/60:.1f} min)")
print(f"peak RSS: {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1e6:.2f} GB")
