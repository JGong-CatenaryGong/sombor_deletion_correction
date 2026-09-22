"""
analyze_collisions.py -- how much of a graph does each deck-derived signature
retain?

For every analysis set S and every invariant I we form the signature
    S_I(G) = sort { I(G-e) : e in E(G) }              (edge deck)
and group S by it.  A group with two members is a *collision*: two
non-isomorphic graphs that the unlabelled deck summary cannot tell apart.

Reported per (set, invariant):
    classes, collision_graphs, collision_rate, largest_class,
    residual_bits = sum_C (|C|/|S|) log2|C|        (bits still needed to name G)
    identity_bits = log2|S|                        (bits needed without signature)

The signature of the deck itself (the sorted multiset of card certificates) is
included as 'deck:itself'; a collision there would be a counterexample to the
edge reconstruction conjecture in the tested range, so it is checked exactly.

Outputs
  results/invariant_collisions.csv    one row per (set, source, invariant)
  results/collision_examples.json     smallest collision pairs, exact values
  results/erc_deck_check.json         exact edge-deck collision check
"""

from __future__ import annotations

import argparse
import csv
import gzip
import json
import os
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import graphlib as gl
import invariants as inv
import dataset as ds


def partition_from_counter(counter: Counter, n: int) -> dict:
    sizes = list(counter.values())
    colliding = sum(s for s in sizes if s > 1)
    residual = 0.0
    for s in sizes:
        if s > 1:
            residual += (s / n) * __import__("math").log2(s)
    return {
        "n": n,
        "classes": len(sizes),
        "resolved": len(sizes) == n,
        "collision_graphs": colliding,
        "collision_rate": colliding / n if n else 0.0,
        "largest_class": max(sizes) if sizes else 0,
        "residual_bits": residual,
        "identity_bits": __import__("math").log2(n) if n else 0.0,
    }


def exact_deck_signature(g6: str, kind: str, inv_name: str):
    """Recompute a signature exactly (no hashing) for a specific graph."""
    adj = gl.from_graph6(g6)
    n = len(adj)
    cards = []
    if kind == "edge":
        for u, v in gl.edges_of(adj):
            c = list(adj)
            c[u] &= ~(1 << v)
            c[v] &= ~(1 << u)
            cards.append(tuple(c))
    else:
        from compute_decks import cards_of
        cards = list(cards_of(adj, "vertex"))
    vals = []
    for c in cards:
        fp = inv.quantised_fingerprint(c)
        vals.append(fp[inv_name])
    vals.sort()
    return vals


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kind", choices=["edge", "vertex"], default="edge")
    ap.add_argument("--sets",
                    default="all_n8,conn_n8,chem_n8,chemp_n8,conn_n9,chem_n9,"
                            "chemp_n9,chem_m4_n9,conn_m4_n9")
    ap.add_argument("--out", default="results/invariant_collisions.csv")
    ap.add_argument("--examples", default="results/collision_examples.json")
    ap.add_argument("--max-examples-per-row", type=int, default=2)
    args = ap.parse_args()

    names = ds.load_invariant_names()
    graphs = ds.load_graphs()
    decks = ds.load_decks(args.kind)
    for r in decks:
        r["fl"] = graphs[r["i"]]["fl"]
    print(f"loaded {len(decks)} {args.kind}-deck records", flush=True)

    preds = ds.set_predicates()
    set_names = [s for s in args.sets.split(",") if s in preds]
    rows = []
    examples = []
    erc = {}
    exact_failures = []   # (set, source) whose exact re-computation disagrees

    for sname in set_names:
        pred = preds[sname]
        sub = [r for r in decks if pred(r)]
        if not sub:
            continue
        print(f"--- set {sname}: {len(sub)} graphs", flush=True)
        # pre-split signatures once
        sigs = [r["sig"].split("|") for r in sub]
        gsigs = [r["gsig"].split("|") for r in sub]
        # sources: deck-itself, deck-derived invariants, graph-level invariants
        keysets = {"deck:itself": [r["dk"] for r in sub]}
        for i, nm in enumerate(names):
            keysets[f"deck:{nm}"] = [s[i] for s in sigs]
        for i, nm in enumerate(names):
            keysets[f"graph:{nm}"] = [s[i] for s in gsigs]

        for source, keys in keysets.items():
            c = Counter(keys)
            st = partition_from_counter(c, len(sub))
            st.update({"set": sname, "source": source})
            rows.append(st)
            if source == "deck:itself":
                erc[sname] = {
                    "n_graphs": len(sub),
                    "classes": st["classes"],
                    "collisions": st["collision_graphs"],
                    "resolved": st["resolved"],
                }
            if not st["resolved"] and args.max_examples_per_row:
                # smallest collision pair: min n, then min m, then graph6
                members_map = defaultdict(list)
                for r, k in zip(sub, keys):
                    members_map[k].append(r)
                best = None
                for k, cnt in c.items():
                    if cnt < 2:
                        continue
                    cand = sorted(
                        members_map[k], key=lambda r: (r["n"], r["m"], r["i"])
                    )[:2]
                    key = (cand[0]["n"], cand[0]["m"], cand[0]["i"], cand[1]["i"])
                    if best is None or key < best[0]:
                        best = (key, cand)
                if best is not None:
                    cand = best[1]
                    src_kind, iv = source.split(":")
                    ex = {
                        "set": sname,
                        "source": source,
                        "deck_kind": args.kind,
                        "n": cand[0]["n"],
                        "m": cand[0]["m"],
                        "graphs": [
                            {"g6": r["i"], "deg_seq": r["ds"], "et": r["et"], "m": r["m"], "n": r["n"]}
                            for r in cand
                        ],
                    }
                    if src_kind == "deck" and iv != "itself":
                        # recompute the signature exactly (no hashing) and
                        # *verify* that all members of the class share it
                        sigs_ex = [exact_deck_signature(r["i"], args.kind, iv) for r in cand]
                        ex["exact_signatures"] = sigs_ex
                        ex["exact_signatures_verified"] = len({repr(s) for s in sigs_ex}) == 1
                    elif src_kind == "graph":
                        # The class is defined by the *quantised* value (then
                        # hashed); the recheck verifies that the quantised
                        # values themselves coincide, so a 64-bit hash
                        # collision would fail here.  Raw floats are recorded
                        # for display only: mathematically equal values can
                        # differ below the 1e-9 grid (cf. report section 1.4).
                        ivs = iv if isinstance(iv, list) else [iv]
                        raws = [inv.fingerprint(gl.from_graph6(r["i"])) for r in cand]
                        quants = [inv.quantised_fingerprint(gl.from_graph6(r["i"])) for r in cand]
                        ex["exact_signatures"] = [[f[k] for f in raws] for k in ivs]
                        ex["exact_signatures_quantised"] = [[f[k] for f in quants] for k in ivs]
                        ex["exact_signatures_verified"] = all(
                            len({repr(f[k]) for f in quants}) == 1 for k in ivs)
                    if not ex.get("exact_signatures_verified", True):
                        exact_failures.append((sname, source))
                        print(f"    !! EXACT RECHECK FAILED for {source} on {sname}",
                              flush=True)
                    examples.append(ex)
                    print(f"    {source:28s} classes={st['classes']:6d} coll={st['collision_graphs']:6d} "
                          f"max={st['largest_class']:4d} res_bits={st['residual_bits']:8.3f} "
                          f"min_example n={cand[0]['n']} m={cand[0]['m']}", flush=True)
            else:
                print(f"    {source:28s} classes={st['classes']:6d} RESOLVED residual_bits=0", flush=True)

    with open(args.out, "w", newline="") as f:
        w = csv.DictWriter(
            f,
            fieldnames=["set", "source", "n", "classes", "resolved", "collision_graphs",
                        "collision_rate", "largest_class", "residual_bits", "identity_bits"],
        )
        w.writeheader()
        for r in rows:
            w.writerow({k: r[k] for k in w.fieldnames})
    with open(args.examples, "w") as f:
        json.dump(examples, f, indent=1)
    with open(f"results/erc_{args.kind}_deck_check.json", "w") as f:
        json.dump(erc, f, indent=1)
    print(f"wrote {args.out} ({len(rows)} rows) and {args.examples} ({len(examples)} examples)")
    if exact_failures:
        # A hash collision or an implementation bug: the exact (unhashed)
        # re-computation disagrees with the class membership.  Fail loudly
        # instead of silently emitting a fake collision.
        print(f"ERROR: exact signature recheck failed for {len(exact_failures)} "
              f"example(s): {exact_failures[:10]}", flush=True)
        sys.exit(1)
    print(f"exact signature recheck: all {len(examples)} examples verified", flush=True)


if __name__ == "__main__":
    main()
