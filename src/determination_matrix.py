"""
determination_matrix.py -- what does each deck signature actually determine?

For a signature S (a deck-derived or graph-level summary of G) and a target T we
ask and quantify:

  determined(S,T) : is T constant on every class of graphs sharing S?
  I(S;T)          : empirical mutual information of the two partitions (bits)
  H(T|S)          : remaining uncertainty about T given S (bits)

The result is the information-content table of the report: it shows, e.g., that
the multiset of degrees of the cards determines the degree sequence, while the
multiset {SO(G-e)} determines neither the degree sequence nor the edge-type
multiset nor SO(G) itself.

The C target uses a *sound* key (review item: the earlier round(C, 6) could in
principle merge genuinely different C values).  Since C is a function of the
edge-type multiset (report section 7.7, exhaustively verified), the key is
computed once per multiset (so equal multisets always get identical floats) and
values of different multisets that fall within 2e-9 are merged only when they
are *exactly* equal at 50-digit precision.  Genuine C gaps on n <= 9 are at
least 3.2e-8 (measured; e.g. 20 near-coincident pairs on conn_m4_n9), far above
the merge threshold, and the script fails loudly if that ever changes.

Output: results/determination_matrix.csv
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import math

import mpmath as mp

import graphlib as gl
import dataset as ds

DECK_SIGNATURES = [
    "deg_seq", "edge_types", "n_comp", "comp_sizes", "tri", "clique", "chrom",
    "girth", "n_bridges", "n_cut", "diam", "dist_dist", "match_poly", "taus",
    "sombor", "sombor_inv", "randic", "abc", "m1", "m2", "wiener",
    "adj_spec", "lap_spec", "q_spec", "adj_charpoly", "lap_charpoly", "energy",
]
TARGETS = [
    ("ds", "degree sequence of G"),
    ("ds_sig", "multiset of degree sequences of the cards"),
    ("et", "multiset of edge degree-types of G"),
    ("so", "Sombor index SO(G)"),
    ("dd", "multiset {Delta_e}"),
    ("taus", "number of spanning trees"),
    ("tri", "number of triangles"),
    ("wiener", "Wiener index"),
    ("n", "order n"),
    ("m", "size m"),
    ("C", "Sombor deletion correction C(G)"),
]

# merge threshold for the sound C key: far below the smallest *genuine* gap
# between C values of distinct edge-type multisets (3.2e-8, measured on
# n <= 9) and far above the float noise of the per-multiset computation (~1e-13)
_C_MERGE_EPS = 2e-9
_MP_DPS = 50


def _c_float(et: str) -> float:
    """C as a function of the edge-type multiset (float, canonical per et)."""
    tot = 0.0
    for tok in et.split(","):
        if not tok:
            continue
        a, b = (int(x) for x in tok.split("-"))
        tot += (a - 1) * (math.sqrt(a * a + b * b) - math.sqrt((a - 1) ** 2 + b * b))
        tot += (b - 1) * (math.sqrt(b * b + a * a) - math.sqrt((b - 1) ** 2 + a * a))
    return tot


def _c_exact(et: str):
    """C of one edge-type multiset at high precision (merging decisions only)."""
    tot = mp.mpf(0)
    for tok in et.split(","):
        if not tok:
            continue
        a, b = (int(x) for x in tok.split("-"))
        tot += (a - 1) * (mp.sqrt(a * a + b * b) - mp.sqrt((a - 1) ** 2 + b * b))
        tot += (b - 1) * (mp.sqrt(b * b + a * a) - mp.sqrt((b - 1) ** 2 + a * a))
    return tot


def sound_C_keys(ets, sname):
    """Sound quantisation of the C target.

    Returns (key per graph, number of distinct C values).  Equal multisets get
    identical keys by construction; near-coincident values of *different*
    multisets are merged only on proven exact equality, so genuinely different
    C values are never merged.
    """
    vals = {e: _c_float(e) for e in set(ets)}
    items = sorted(vals.items(), key=lambda kv: kv[1])
    groups: list[list] = []          # [rep_et, member_ets, max_float]
    for e, v in items:
        if groups and v - groups[-1][2] < _C_MERGE_EPS:
            g = groups[-1]
            if _c_exact(e) == _c_exact(g[0]):
                g[1].append(e)
                g[2] = max(g[2], v)
                continue
            raise SystemExit(
                f"ERROR: C key unsafe on set {sname}: genuine C gap "
                f"{v - groups[-1][2]:.2e} <= merge threshold {_C_MERGE_EPS:.0e}; "
                "the threshold must be lowered before trusting this run.")
        groups.append([e, [e], v])
    gid = {}
    for i, (_rep, members, _v) in enumerate(groups):
        for e in members:
            gid[e] = i
    return [gid[e] for e in ets], len(groups)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kind", default="edge")
    ap.add_argument("--sets", default="chem_n9,chemp_n9,chem_n8,conn_n8,all_n8,conn_n9")
    ap.add_argument("--out", default="results/determination_matrix.csv")
    args = ap.parse_args()

    names = ds.load_invariant_names()
    graphs = ds.load_graphs()
    decks = ds.load_decks(args.kind)
    for r in decks:
        r["fl"] = graphs[r["i"]]["fl"]
    preds = ds.set_predicates()
    rows = []
    for sname in [s for s in args.sets.split(",") if s in preds]:
        sub = [r for r in decks if preds[sname](r)]
        if not sub:
            continue
        sigs = [r["sig"].split("|") for r in sub]
        # Sound C target key: computed once per edge-type multiset, with
        # near-coincident values merged only on proven exact equality
        # (determination counts are unchanged; this removes the theoretical
        # "fake determined" risk of the earlier round(C, 6) quantisation).
        Ckeys, n_distinct_C = sound_C_keys([r["et"] for r in sub], sname)
        print(f"    C target: {n_distinct_C} distinct sound values", flush=True)
        targets = {
            "ds": [r["ds"] for r in sub],
            "ds_sig": [s[names.index("deg_seq")] for s in sigs],
            "et": [r["et"] for r in sub],
            "so": [r["so"] for r in sub],
            "dd": [r["dd"] for r in sub],
            "taus": [_dec(r, names, "taus") for r in sub],
            "tri": [_dec(r, names, "tri") for r in sub],
            "wiener": [_dec(r, names, "wiener") for r in sub],
            "n": [r["n"] for r in sub],
            "m": [r["m"] for r in sub],
            "C": Ckeys,
        }
        for sig_name in DECK_SIGNATURES:
            keys = [s[names.index(sig_name)] for s in sigs]
            for tkey, tdesc in TARGETS:
                tvals = targets[tkey]
                mi, h_cond = ds.mutual_information(keys, tvals)
                rows.append({
                    "set": sname, "n_graphs": len(sub),
                    "signature": f"deck:{sig_name}",
                    "target": tkey, "target_desc": tdesc,
                    "determined": ds.determines(keys, tvals),
                    "H_target": round(ds.entropy(__import__("collections").Counter(tvals).values()), 6),
                    "I_signature_target": round(mi, 6),
                    "H_target_given_signature": round(h_cond, 6),
                })
        print(f"set {sname}: done ({len(sub)} graphs, {len(DECK_SIGNATURES)} signatures)", flush=True)

    with open(args.out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    print(f"wrote {args.out} ({len(rows)} rows)")


def _dec(r, names, key):
    return r["dec"][__import__("compute_decks", fromlist=["DEC_KEYS"]).DEC_KEYS.index(key)]


if __name__ == "__main__":
    main()
