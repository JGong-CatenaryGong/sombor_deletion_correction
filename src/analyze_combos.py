"""
analyze_combos.py -- minimal combinations of invariants that reconstruct.

Given a set of graphs and a pool of signatures (each signature being either

    deck-derived:  S_I(G) = sort { I(G-e) : e in E(G) }        ('deck:I')
    graph-level :  I(G) itself                                  ('graph:I')

this script finds combinations whose *joint* signature separates every
isomorphism class in the set.  Ambiguity is always decided on the **joint key**
of the signatures selected so far: two graphs are still confused only if they
agree on *every* selected signature.  (An earlier version refined a
mixed-class index set one signature at a time, which could declare a pair
unresolved when the graphs involved shared different signatures with different
partners; that inflated every combination size.  See report section 6.)

Search performed:

  * all resolving singles (exhaustive);
  * all resolving pairs (exhaustive over the pool, joint keys);
  * resolving triples: only when no pair resolves, and only for pairs whose
    ambiguity set has at most ``--triple-cap`` graphs (otherwise recorded as
    skipped, so the cost stays bounded);
  * a greedy forward combination (at each step the signature that minimises the
    residual bits of the joint key on the graphs still ambiguous);
  * a backward-minimal combination (start from the full pool, drop every
    signature whose removal keeps the combination resolving) -- an irreducible
    combination, hence an upper bound on the minimum size.

Outputs
  results/combos_<set>.json      full result for one set
  results/combos_summary.csv     one row per (set, pool)

Note: the greedy and backward-minimal sets are heuristic/irreducible bounds,
not certified minima; a resolving pair of size 2 (when one exists) is the true
minimum.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import dataset as ds


def residual_bits(keys) -> float:
    c = Counter(keys)
    n = len(keys)
    return sum((v / n) * math.log2(v) for v in c.values() if v > 1)


def ambiguous_indices(keys, idxs):
    """Indices of graphs that share their key with another graph in idxs."""
    c = Counter(keys[i] for i in idxs)
    return [i for i in idxs if c[keys[i]] > 1]


def joint_key(pool_keys, names, i):
    return tuple(pool_keys[nm][i] for nm in names)


def ambiguous_joint(pool_keys, names, idxs):
    """Indices in idxs that share their *joint* key over ``names`` with another."""
    c = Counter(joint_key(pool_keys, names, i) for i in idxs)
    return [i for i in idxs if c[joint_key(pool_keys, names, i)] > 1]


def joint_residual_bits(pool_keys, names, idxs) -> float:
    c = Counter(joint_key(pool_keys, names, i) for i in idxs)
    n = len(idxs)
    return sum((v / n) * math.log2(v) for v in c.values() if v > 1)


def is_resolving(keys, idxs) -> bool:
    return len(set(keys[i] for i in idxs)) == len(idxs)


def is_resolving_joint(pool_keys, names, idxs) -> bool:
    return not ambiguous_joint(pool_keys, names, idxs)


def greedy(pool_keys: dict, n: int, idxs=None):
    """Forward selection on joint keys: repeatedly add the signature that
    minimises the residual bits of the joint key on the still-ambiguous graphs."""
    chosen: list[str] = []
    remaining = set(pool_keys)
    cur = list(range(n)) if idxs is None else list(idxs)
    while cur and remaining:
        best = None
        for name in remaining:
            rb = joint_residual_bits(pool_keys, chosen + [name], cur)
            if best is None or rb < best[0] - 1e-12:
                best = (rb, name)
        if best is None:
            break
        _, name = best
        chosen.append(name)
        remaining.discard(name)
        cur = ambiguous_joint(pool_keys, chosen, list(range(n)))
        if not cur:
            break
    return chosen, cur


def backward_minimal(pool_keys: dict, n: int, order=None):
    """Drop every signature whose removal keeps the joint key resolving."""
    names = list(order or pool_keys)
    active = list(names)
    if not is_resolving_joint(pool_keys, active, list(range(n))):
        return None
    for nm in names:
        trial = [x for x in active if x != nm]
        if is_resolving_joint(pool_keys, trial, list(range(n))):
            active = trial
    return active


def resolving_triples(pool_keys: dict, n: int, cap: int = 2000, limit: int = 20):
    """Triples (a, b, c) whose joint key resolves, searched only for pairs that
    do not resolve and whose ambiguity set is at most ``cap`` graphs."""
    idxs_all = list(range(n))
    items = sorted(pool_keys.items())
    found: list[list[str]] = []
    skipped = 0
    for a in range(len(items)):
        for b in range(a + 1, len(items)):
            names = [items[a][0], items[b][0]]
            amb = ambiguous_joint(pool_keys, names, idxs_all)
            if not amb:
                continue                      # already a resolving pair
            if len(amb) > cap:
                skipped += 1
                continue
            for c in range(len(items)):
                nm = items[c][0]
                if nm in names:
                    continue
                if is_resolving_joint(pool_keys, names + [nm], amb):
                    found.append(names + [nm])
                    break
            if len(found) >= limit:
                return found, skipped
    return found, skipped


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kind", default="edge")
    ap.add_argument("--sets", default="chem_n8,chemp_n8,chem_n9,chemp_n9,conn_n8,all_n8")
    ap.add_argument("--pairs", action="store_true", default=True)
    ap.add_argument("--triples", action="store_true", default=True,
                    help="search resolving triples when no pair resolves")
    ap.add_argument("--triple-cap", type=int, default=2000,
                    help="skip a pair in the triple search if more graphs are ambiguous")
    ap.add_argument("--outdir", default="results")
    args = ap.parse_args()

    names = ds.load_invariant_names()
    graphs = ds.load_graphs()
    decks = ds.load_decks(args.kind)
    for r in decks:
        r["fl"] = graphs[r["i"]]["fl"]
    preds = ds.set_predicates()
    summary = []

    for sname in [s for s in args.sets.split(",") if s in preds]:
        sub = [r for r in decks if preds[sname](r)]
        if not sub:
            continue
        n = len(sub)
        sigs = [r["sig"].split("|") for r in sub]
        gsigs = [r["gsig"].split("|") for r in sub]
        pools = {
            "DECK": {f"deck:{nm}": [s[i] for s in sigs] for i, nm in enumerate(names)},
            "GRAPH": {f"graph:{nm}": [s[i] for s in gsigs] for i, nm in enumerate(names)},
        }
        pools["MIXED"] = {**pools["DECK"], **pools["GRAPH"]}
        print(f"=== set {sname}: {n} graphs", flush=True)
        result = {"set": sname, "n": n, "pools": {}}

        for pname, pool in pools.items():
            info = {"n_signatures": len(pool)}
            singles = [nm for nm, k in pool.items() if is_resolving(k, list(range(n)))]
            info["resolving_singles"] = sorted(singles)
            print(f"  [{pname}] resolving singles: {len(singles)} -> {sorted(singles)[:8]}",
                  flush=True)

            pair_list = []
            if args.pairs and not singles:
                items = sorted(pool.items())
                for a in range(len(items)):
                    ka = items[a][1]
                    for b in range(a + 1, len(items)):
                        kb = items[b][1]
                        if is_resolving(list(zip(ka, kb)), list(range(n))):
                            pair_list.append([items[a][0], items[b][0]])
                info["resolving_pairs_count"] = len(pair_list)
                info["resolving_pairs_examples"] = pair_list[:20]
                print(f"  [{pname}] resolving pairs: {len(pair_list)}", flush=True)
            else:
                info["resolving_pairs_count"] = None

            triples: list[list[str]] = []
            triples_skipped = 0
            if args.triples and not singles and not pair_list:
                triples, triples_skipped = resolving_triples(pool, n, cap=args.triple_cap)
                print(f"  [{pname}] resolving triples found: {len(triples)} "
                      f"(pairs skipped: {triples_skipped})", flush=True)
            info["resolving_triples_count"] = len(triples)
            info["resolving_triples_examples"] = triples[:5]
            info["resolving_triples_pairs_skipped"] = triples_skipped

            greedy_combo, left = greedy(pool, n)
            info["greedy"] = greedy_combo
            info["greedy_ambiguous_left"] = len(left)
            bm = backward_minimal(pool, n)
            info["backward_minimal"] = bm
            info["backward_minimal_size"] = len(bm) if bm else None
            print(f"  [{pname}] greedy={greedy_combo} (ambiguous left {len(left)}), "
                  f"backward-minimal size={info['backward_minimal_size']}", flush=True)
            result["pools"][pname] = info
            summary.append({
                "set": sname, "n_graphs": n, "pool": pname,
                "n_resolving_singles": len(singles),
                "resolving_singles": ";".join(sorted(singles)[:12]),
                "n_resolving_pairs": info["resolving_pairs_count"],
                "min_pair_example": ";".join(pair_list[0]) if pair_list else "",
                "n_resolving_triples": len(triples),
                "min_triple_example": ";".join(triples[0]) if triples else "",
                "backward_minimal_size": info["backward_minimal_size"],
                "backward_minimal": ";".join(bm or []),
                "greedy_size": len(greedy_combo),
                "greedy": ";".join(greedy_combo),
            })

        with open(f"{args.outdir}/combos_{sname}.json", "w") as f:
            json.dump(result, f, indent=1)

    with open(f"{args.outdir}/combos_summary.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(summary[0].keys()))
        w.writeheader()
        w.writerows(summary)
    print(f"wrote {args.outdir}/combos_summary.csv")


if __name__ == "__main__":
    main()
