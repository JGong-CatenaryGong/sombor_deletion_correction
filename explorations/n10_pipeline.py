"""
n10_pipeline.py -- item 5 A/B: CHEM n=10 (connected, Delta<=4) and CHEMP n=10
(connected, planar, Delta<=4) through the key parts of the frozen pipeline.

Per graph (deck-only quantities are marked *):
  ds, m, edge-type multiset, C (float + exact multiquadratic coordinate vector),
  psiSum, *edge-deck signature (sorted card certificates), *Sombor-deck signature,
  *edge-type-deck signature (sorted per-card edge-type vectors),
  *degree sequence recovered from the deck (Lemma 2 / report 10.1),
  *A1 linear-system recovery verdict (full recovery <-> 2*Delta <= m).

Aggregations written to results/n10_chem_summary.json:
  deck collision classes (all / with m>=4), Sombor-deck vs edge-type-deck
  partition identity, A1 criterion contingency table, Delta coincidence scan
  (exact normal forms), C exact-collision scan modulo matching direction,
  minimum true gap between distinct exact C values, deck->degree-sequence failures.
Per-graph records: results/n10_chem.jsonl.gz
"""
import os
import sys
import json
import math
import gzip
import time
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, ".pylibs"))
sys.path.insert(0, os.path.join(ROOT, "src"))
import graphlib as gl

SQRT2 = math.sqrt(2.0)


# ---------- exact coordinate machinery (A3) ----------
def sqrt_vec(N):
    g, d, n = 1, 2, N
    while d * d <= n:
        while n % (d * d) == 0:
            n //= d * d
            g *= d
        d += 1
    return {n: g}


def vadd(a, b):
    o = dict(a)
    for k, v in b.items():
        o[k] = o.get(k, 0) + v
        if o[k] == 0:
            del o[k]
    return o


def vmul(a, k):
    return {s: g * k for s, g in a.items()} if k else {}


PHI = {}


def phi_vec(x, y):
    if (x, y) not in PHI:
        v = vmul(sqrt_vec(x * x + y * y), x + y - 2)
        v = vadd(v, vmul(sqrt_vec((x - 1) ** 2 + y * y), -(x - 1)))
        v = vadd(v, vmul(sqrt_vec((y - 1) ** 2 + x * x), -(y - 1)))
        PHI[(x, y)] = v
    return PHI[(x, y)]


C_FLOAT = {}


def phi_float(x, y):
    if (x, y) not in C_FLOAT:
        c1 = math.sqrt(x * x + y * y) - math.sqrt((x - 1) ** 2 + y * y)
        c2 = math.sqrt(x * x + y * y) - math.sqrt((y - 1) ** 2 + x * x)
        C_FLOAT[(x, y)] = (x - 1) * c1 + (y - 1) * c2
    return C_FLOAT[(x, y)]


def key_of(a, b):
    return (a, b) if a <= b else (b, a)


# ---------- deck machinery ----------
def ordered_N(adj):
    d = gl.degrees(adj)
    N = Counter()
    for u, v in gl.edges_of(adj):
        N[(d[u], d[v])] += 1
        N[(d[v], d[u])] += 1
    return N


def recover(m, LHS, Delta, want_trace=False):
    """Back-substitution; returns (R, fully_recovered, undetermined_with_truth)."""
    R = {}
    ok = True
    for s in range(m + 1, -1, -1):
        for x in range(0, s + 1):
            y = s - x
            if x > Delta or y > Delta:
                R[(x, y)] = 0
                continue
            coef = m - s + 1
            lhs = LHS.get((x, y), 0)
            if coef <= 0:
                assert lhs == 0, ("identity violation", x, y)
                R[(x, y)] = None
                ok = False
                continue
            a, b = R[(x + 1, y)], R[(x, y + 1)]
            if a is None or b is None:
                R[(x, y)] = None
                ok = False
            else:
                val = (lhs - x * a - y * b) / coef
                if val != int(val) or val < 0:
                    return R, False, ["nonintegral"]
                R[(x, y)] = int(val)
    undet = sorted(k for k, v in R.items() if v is None)
    return R, ok, undet


def degree_seq_from_deck(cards, m):
    c_x = Counter()
    for c in cards:
        for d in gl.degrees(c):
            c_x[d] += 1
    X = max(c_x) if c_x else 0
    n = {X + 1: 0}
    for x in range(X, 0, -1):
        num = c_x.get(x, 0) - (x + 1) * n[x + 1]
        den = m - x
        if den <= 0 or num % den or num // den < 0:
            return None
        n[x] = num // den
    return sorted([x for x, c in n.items() for _ in range(c)], reverse=True)


SCALE = 10 ** 9


def card_so(c):
    """Quantised card Sombor value (invariants.Q = round(1e9 * x), the frozen
    n<=9 convention).  A raw float sum is polluted by summation-order noise,
    which artificially splits Sombor-deck classes."""
    d = gl.degrees(c)
    tot = 0.0
    for u, v in gl.edges_of(c):
        tot += math.sqrt(d[u] * d[u] + d[v] * d[v])
    return int(round(tot * SCALE))


def card_et_key(c):
    d = gl.degrees(c)
    return tuple(sorted((min(d[u], d[v]), max(d[u], d[v])) for u, v in gl.edges_of(c)))


def main():
    t0 = time.perf_counter()
    lv = gl.enumerate_graphs_by_order(10, maxdeg=4)
    all10 = list(lv[10].values())
    chem = [a for a in all10 if gl.connected(a)]
    print(f"deg<=4 n=10: {len(all10)}; connected (CHEM): {len(chem)} "
          f"[{time.perf_counter()-t0:.1f}s]", flush=True)

    import networkx as nx
    planar_flags = {}
    chempl = []
    for a in chem:
        G = nx.Graph()
        G.add_nodes_from(range(10))
        G.add_edges_from(gl.edges_of(a))
        pl = bool(nx.check_planarity(G)[0])
        planar_flags[a] = pl
        if pl:
            chempl.append(a)
    print(f"CHEMP n=10: {len(chempl)}", flush=True)

    deck_class = defaultdict(list)          # edge-deck signature -> [g6]
    sodeck_class = defaultdict(list)        # Sombor-deck signature -> [g6]
    etdeck_class = defaultdict(list)        # edge-type-deck signature -> [g6]
    et_class = defaultdict(list)            # edge-type multiset -> [g6]
    a1_table = Counter()
    ds_fail = []
    delta_groups = defaultdict(set)         # Delta exact vector key -> set of types
    c_groups = defaultdict(set)             # exact C vector -> set of stripped ets
    distinct_C = {}
    collisions_with_m4 = []
    recs = []

    for idx, a in enumerate(chem):
        g6 = gl.to_graph6(a)
        ds = gl.degrees(a)
        m = gl.n_edges(a)
        Delta = max(ds)
        cards, card_certs, card_sos, card_ets = [], [], [], []
        for u, v in gl.edges_of(a):
            c = list(a)
            c[u] &= ~(1 << v)
            c[v] &= ~(1 << u)
            c = tuple(c)
            cards.append(c)
            card_certs.append(gl.canon_cert_hex(c))
            card_sos.append(card_so(c))
            card_ets.append(card_et_key(c))
        LHS = Counter()
        for c in cards:
            LHS.update(ordered_N(c))
        R, full, undet = recover(m, LHS, Delta)
        truth = ordered_N(a)

        # A1 criterion contingency
        crit = 2 * Delta <= m
        a1_table[("recovered" if full else "not", "crit" if crit else "degenerate")] += 1
        if (not crit) and full:
            a1_table["crit-violation"] += 1

        # deck -> degree sequence
        ds_rec = degree_seq_from_deck(cards, m)
        if ds_rec != sorted(ds, reverse=True):
            ds_fail.append({"g6": g6, "m": m, "ds": ",".join(map(str, ds))})

        # edge-type multiset + C + Delta configs
        et = Counter()
        cvec = {}
        C = 0.0
        for u, v in gl.edges_of(a):
            k = key_of(ds[u], ds[v])
            et[k] += 1
            C += phi_float(*k)
            cvec = vadd(cvec, phi_vec(*k))
        etk = tuple(sorted(et.items()))
        etstrip = tuple(sorted((k, c) for k, c in et.items() if k != (1, 1)))
        et_class[etk].append(g6)
        deck_class[tuple(sorted(card_certs))].append(g6)
        sodeck_class[tuple(sorted(card_sos))].append(g6)
        etdeck_class[tuple(sorted(card_ets))].append(g6)
        ck = tuple(sorted(cvec.items()))
        c_groups[ck].add(etstrip)
        distinct_C.setdefault(ck, C)

        # per-edge Delta configurations (d_u, d_v, neighbour-degree multisets of both ends)
        deg = list(ds)
        for u, v in gl.edges_of(a):
            nu = sorted(deg[i] for i in range(len(a)) if (a[u] >> i) & 1 and i != v)
            nv = sorted(deg[i] for i in range(len(a)) if (a[v] >> i) & 1 and i != u)
            vec = sqrt_vec(deg[u] ** 2 + deg[v] ** 2)
            for x in nu:
                vec = vadd(vec, vmul(sqrt_vec(deg[u] ** 2 + x * x), 1))
                vec = vadd(vec, vmul(sqrt_vec((deg[u] - 1) ** 2 + x * x), -1))
            for x in nv:
                vec = vadd(vec, vmul(sqrt_vec(deg[v] ** 2 + x * x), 1))
                vec = vadd(vec, vmul(sqrt_vec((deg[v] - 1) ** 2 + x * x), -1))
            delta_groups[tuple(sorted(vec.items()))].add(key_of(deg[u], deg[v]))
        recs.append({"g6": g6, "m": m, "ds": ",".join(map(str, ds)),
                     "pl": int(planar_flags[a]), "C": C,
                     "cvec": sorted(cvec.items()), "et": [[k[0], k[1], c] for k, c in et.items()]})
        if (idx + 1) % 20000 == 0:
            print(f"  {idx+1}/{len(chem)} [{time.perf_counter()-t0:.0f}s]", flush=True)
    print(f"per-graph pass done [{time.perf_counter()-t0:.0f}s]", flush=True)

    # ---- deck collisions ----
    def collision_stats(cls):
        n_cls = len(cls)
        coll = {k: v for k, v in cls.items() if len(v) > 1}
        m4 = []
        for k, v in coll.items():
            metas = [(g, rec_by_g6[g]) for g in v]
            if any(mm["m"] >= 4 for _, mm in metas):
                m4.append([g for g, _ in metas])
        return n_cls, len(coll), m4

    rec_by_g6 = {r["g6"]: r for r in recs}
    n_deck, n_deck_coll, coll_m4 = collision_stats(deck_class)
    n_so, n_so_coll, so_m4 = collision_stats(sodeck_class)
    n_etdeck, n_etdeck_coll, _ = collision_stats(etdeck_class)
    n_et, n_et_coll, _ = collision_stats(et_class)

    # partition identity: deck signature and Sombor-deck signature induce the same partition
    def partition_map(cls):
        pos = {}
        for i, (k, v) in enumerate(cls.items()):
            for g in v:
                pos[g] = i
        return pos

    def refines(fine, coarse):
        seen = {}
        for g, k in fine.items():
            c = coarse[g]
            if seen.setdefault(k, c) != c:
                return False
        return True

    pd, ps = partition_map(deck_class), partition_map(sodeck_class)
    pe = partition_map(etdeck_class)
    same_partition = refines(pd, ps) and refines(ps, pd)
    refines_flag = refines(ps, pd)      # Sombor-deck partition refines edge-deck partition
    same_so_etdeck = refines(ps, pe) and refines(pe, ps)   # partition identity (Prop. 12)

    # ---- C collisions (modulo matching direction) + min gap ----
    c_coll = {k: v for k, v in c_groups.items() if len(v) > 1 and k != ()}
    vals = sorted(distinct_C.items(), key=lambda kv: kv[1])
    min_gap, gap_pair = None, None
    for i in range(1, len(vals)):
        d = vals[i][1] - vals[i - 1][1]
        if d > 1e-12 and (min_gap is None or d < min_gap):
            min_gap, gap_pair = d, [vals[i - 1][1], vals[i][1]]

    # ---- Delta coincidence scan over appearing configurations ----
    delta_cross = {k: v for k, v in delta_groups.items() if len(v) > 1}

    summary = {
        "script": "explorations/n10_pipeline.py",
        "CHEM_n10": len(chem), "CHEMP_n10": len(chempl),
        "A1_criterion": {f"{a}/{b}": c for (a, b), c in a1_table.items()},
        "deck": {"n_classes": n_deck, "n_collision_classes": n_deck_coll,
                 "collisions_with_m_ge_4": coll_m4[:10],
                 "sombor_deck": {"n_classes": n_so, "n_collision_classes": n_so_coll},
                 "edge_type_deck": {"n_classes": n_etdeck, "n_collision_classes": n_etdeck_coll},
                 "edge_type_multiset": {"n_classes": n_et, "n_collision_classes": n_et_coll},
                 "sombor_eq_edge_type_deck_partition": same_so_etdeck,
                 "deck_eq_sombor_deck_partition": same_partition,
                 "sombor_deck_refines_deck": refines_flag},
        "deck_to_degree_seq_failures": ds_fail[:10],
        "n_deck_to_degree_seq_failures": len(ds_fail),
        "C": {"n_distinct_exact_values": len(distinct_C),
              "n_collisions_mod_matching": len(c_coll),
              "min_true_gap": min_gap, "min_gap_pair": gap_pair},
        "Delta": {"n_config_values": len(delta_groups),
                  "n_cross_type_groups": len(delta_cross),
                  "cross_type_groups": [[list(t) for t in v] for v in list(delta_cross.values())[:10]]},
        "runtime_s": time.perf_counter() - t0,
    }
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    with open(os.path.join(HERE, "results", "n10_chem_summary.json"), "w") as f:
        json.dump(summary, f, indent=1)
    with gzip.open(os.path.join(HERE, "results", "n10_chem.jsonl.gz"), "wt") as f:
        for r in recs:
            f.write(json.dumps(r) + "\n")
    print(json.dumps(summary, indent=1)[:4000])
    print("wrote results/n10_chem_summary.json + n10_chem.jsonl.gz")


if __name__ == "__main__":
    main()
