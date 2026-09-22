"""
n10_deck_partition.py -- replicate the report's deck-partition identity on the
CHEM n=10 set (89,402 connected graphs with Delta<=4):

  deck signature      : sorted multiset of card isomorphism certificates
  edge-type signature : sorted multiset of the per-card edge-type vectors
                        (the "edge-type deck" of report section 7.6)
  Sombor signature    : sorted multiset of the quantised card Sombor values
                        (invariants.Q, as in the frozen n<=9 pipeline)

Checks:  (a) deck refines edge-type signature;
         (b) Sombor signature and edge-type signature induce the SAME partition
             (the report's partition identity, verified at n<=9);
         (c) collision counts of each signature (a collision class = two graphs
             sharing the signature).
"""
import os
import sys
import json
import math
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, ".pylibs"))
sys.path.insert(0, os.path.join(ROOT, "src"))
import graphlib as gl


def edge_type_key(adj):
    d = gl.degrees(adj)
    return tuple(sorted((min(d[u], d[v]), max(d[u], d[v])) for u, v in gl.edges_of(adj)))


SCALE = 10 ** 9


def card_so(adj):
    """Quantised card Sombor value (invariants.Q = round(1e9 * x), the frozen
    n<=9 convention).  A raw float sum is polluted by summation-order noise,
    which artificially splits Sombor-deck classes."""
    d = gl.degrees(adj)
    tot = 0.0
    for u, v in gl.edges_of(adj):
        tot += math.sqrt(d[u] * d[u] + d[v] * d[v])
    return int(round(tot * SCALE))


def partitions_equal(p1, p2):
    """p1, p2: dict node -> class id.  Equal iff both refine each other."""
    def refines(a, b):
        seen = {}
        for g, k in a.items():
            c = b[g]
            if seen.setdefault(k, c) != c:
                return False
        return True
    return refines(p1, p2) and refines(p2, p1)


def main():
    lv = gl.enumerate_graphs_by_order(10, maxdeg=4)
    chem = [a for a in lv[10].values() if gl.connected(a)]
    print(f"CHEM n=10: {len(chem)}", flush=True)

    deck_sig, et_sig, so_sig = {}, {}, {}
    n_classes = {"deck": 0, "et": 0, "so": 0}
    coll = {"deck": 0, "et": 0, "so": 0}
    deck_map, et_map, so_map = {}, {}, {}
    seen = {"deck": {}, "et": {}, "so": {}}

    for a in chem:
        g6 = gl.to_graph6(a)
        card_certs, card_ets, card_sos = [], [], []
        for u, v in gl.edges_of(a):
            c = list(a)
            c[u] &= ~(1 << v)
            c[v] &= ~(1 << u)
            c = tuple(c)
            card_certs.append(gl.canon_cert_hex(c))
            card_ets.append(edge_type_key(c))
            card_sos.append(card_so(c))
        keys = {"deck": tuple(sorted(card_certs)),
                "et": tuple(sorted(card_ets)),
                "so": tuple(sorted(card_sos))}
        for name, k in keys.items():
            if k in seen[name]:
                coll[name] += 1
                deck_id = seen[name][k]
            else:
                deck_id = n_classes[name]
                seen[name][k] = deck_id
                n_classes[name] += 1
            {"deck": deck_map, "et": et_map, "so": so_map}[name][g6] = deck_id

    res = {
        "script": "explorations/n10_deck_partition.py",
        "CHEM_n10": len(chem),
        "n_classes": n_classes,
        "n_collision_graphs": coll,
        "deck_refines_edge_type_deck": None,
        "sombor_eq_edge_type_deck_partition": partitions_equal(so_map, et_map),
        "deck_eq_edge_type_deck_partition": partitions_equal(deck_map, et_map),
    }
    # deck refines et-deck
    def refines(a, b):
        s = {}
        for g, k in a.items():
            c = b[g]
            if s.setdefault(k, c) != c:
                return False
        return True
    res["deck_refines_edge_type_deck"] = refines(deck_map, et_map)
    with open(os.path.join(HERE, "results", "n10_deck_partition.json"), "w") as f:
        json.dump(res, f, indent=1)
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
