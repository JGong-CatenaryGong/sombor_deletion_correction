"""
coincidence_classification.py -- persist two claims of report sections 7.3/7.4/7.6
that previously had no output file of their own (review item P25):

  (1) partition comparisons, all from the deck file:
      - deck signature {Delta_e} vs {SO(G-e)} (section 7.3), and
      - deck:sombor vs deck:edge_types (section 7.6: the Sombor deck and the
        edge-type deck induce the same partition);
      for contrast, the graph-level SO(G) vs graph-level edge-type multiset is
      also recorded (SO is a strictly coarser function of the multiset);
  (2) the 12,223 Delta coincidences recorded in results/delta_coincidences.json
      are classified into "trivial" ((a,b) <-> (b,a) symmetry of the same type
      pair) and "cross-type", and every cross-type coincidence is re-verified
      in exact arithmetic with sympy.

Output: results/partition_and_classification.json
"""

from __future__ import annotations

import gzip
import json
import math
import os
import sys
from collections import Counter, defaultdict

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import dataset as ds

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(ROOT, "results")


def partition_stats(keys) -> dict:
    c = Counter(keys)
    sizes = list(c.values())
    n = len(keys)
    return {
        "n": n,
        "classes": len(sizes),
        "collision_graphs": sum(s for s in sizes if s > 1),
        "residual_bits": round(sum((s / n) * math.log2(s) for s in sizes if s > 1), 6),
    }


def same_partition(keys_a, keys_b) -> bool:
    """Two signatures induce the same partition iff each is a refinement of the
    other, i.e. the maps are equal up to relabelling of the values."""
    map_a, map_b = {}, {}
    fwd, bwd = {}, {}
    for a, b in zip(keys_a, keys_b):
        if fwd.setdefault(a, b) != b:
            return False
        if bwd.setdefault(b, a) != a:
            return False
    return True


def delta_of_config(cfg) -> sp.Expr:
    """Exact Delta_e of one local configuration [d_u, d_v, N(u)\\v, N(v)\\u]."""
    du, dv, nu, nv = cfg
    c = lambda a, b: sp.sqrt(a ** 2 + b ** 2) - sp.sqrt((a - 1) ** 2 + b ** 2)
    return (sp.sqrt(du ** 2 + dv ** 2)
            + sum(c(du, x) for x in nu)
            + sum(c(dv, y) for y in nv))


def main() -> int:
    out: dict = {"script": "src/coincidence_classification.py"}

    # ---- (1) partition comparisons from the deck file ---------------------
    names = ds.load_invariant_names()
    et_idx = names.index("edge_types")          # deck:edge_types signature slot
    graphs = ds.load_graphs()
    decks = ds.load_decks("edge")
    for r in decks:
        r["fl"] = graphs[r["i"]]["fl"]
    preds = ds.set_predicates()
    parts = {}
    for sname in ["chem_n9", "chem_m4_n9", "conn_n9", "conn_m4_n9", "all_n8"]:
        sub = [r for r in decks if preds[sname](r)]
        if not sub:
            continue
        dd = [tuple(r["dd"].split(",")) for r in sub]        # {Delta_e} deck signature
        sod = [tuple(r["sod"].split(",")) for r in sub]      # {SO(G-e)} = deck:sombor
        et_deck = [r["sig"].split("|")[et_idx] for r in sub] # deck:edge_types signature
        et = [r["et"] for r in sub]                          # graph-level edge types
        no = [r["so"] for r in sub]                          # graph-level SO(G)
        parts[sname] = {
            "n_graphs": len(sub),
            "delta_edeck": partition_stats(dd),
            "so_ge_edeck": partition_stats(sod),
            "deck_edge_types": partition_stats(et_deck),
            "graph_SO": partition_stats(no),
            "graph_edge_type_multiset": partition_stats(et),
            # deck-level comparisons (the claims of sections 7.3 / 7.6)
            "delta_vs_so_ge_same_partition": same_partition(dd, sod),
            "deck_sombor_vs_deck_edge_types_same_partition": same_partition(sod, et_deck),
            # graph-level comparison: SO(G) is a function of the edge-type
            # multiset but strictly coarser (it merges genuinely different
            # multisets) -- recorded for contrast, NOT the section 7.6 claim.
            "graph_SO_vs_graph_edge_types_same_partition": same_partition(no, et),
        }
        print(f"[{sname}] deck delta / deck SO / deck edge-types / graph et: "
              f"{parts[sname]['delta_edeck']['classes']} / "
              f"{parts[sname]['so_ge_edeck']['classes']} / "
              f"{parts[sname]['deck_edge_types']['classes']} / "
              f"{parts[sname]['graph_edge_type_multiset']['classes']} classes "
              f"(delta==so_ge partition: {parts[sname]['delta_vs_so_ge_same_partition']}, "
              f"deck sombor==deck edge-types partition: "
              f"{parts[sname]['deck_sombor_vs_deck_edge_types_same_partition']})", flush=True)
    out["partitions"] = parts

    # ---- (2) classify the Delta coincidences ------------------------------
    coin = json.load(open(os.path.join(RESULTS, "delta_coincidences.json")))
    trivial, cross, cross_verified, cross_failed = 0, [], 0, []
    for rec in coin["coincidences"]:
        types = [tuple(t) for t in rec["types"]]
        uniq = {tuple(sorted(t)) for t in types}
        if len(uniq) == 1:
            trivial += 1
            continue
        cross.append(rec)
        vals = []
        ok = True
        for cfg in rec["configs"]:
            try:
                vals.append(sp.simplify(delta_of_config(cfg)))
            except Exception:
                ok = False
                break
        if ok and len(vals) >= 2 and all(sp.simplify(v - vals[0]) == 0 for v in vals[1:]):
            cross_verified += 1
        else:
            cross_failed.append(rec)
    out["coincidences"] = {
        "n_distinct_configurations": coin["n_distinct_configurations"],
        "n_distinct_delta_values": coin["n_distinct_delta_values"],
        "n_coincidences": len(coin["coincidences"]),
        "n_trivial_symmetric": trivial,
        "n_cross_type": len(cross),
        "cross_type_verified_symbolically": cross_verified,
        "cross_type_failed": len(cross_failed),
        "cross_type_examples": [
            {"types": [list(t) for t in rec["types"]],
             "delta": rec[list(rec)[0]] if False else rec.get("delta_30") or rec.get("delta"),
             "configs": rec["configs"]} for rec in cross[:6]],
    }
    print(f"coincidences: {len(coin['coincidences'])} total, {trivial} trivial, "
          f"{len(cross)} cross-type ({cross_verified} re-verified in sympy)", flush=True)

    with open(os.path.join(RESULTS, "partition_and_classification.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("wrote results/partition_and_classification.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
