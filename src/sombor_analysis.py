r"""
sombor_analysis.py -- information content of the Sombor index under edge deletion.

Theory developed and verified here
----------------------------------
Let G be a simple graph, e = uv an edge, d_x the degree of x in G and

    c(a, b) = sqrt(a^2 + b^2) - sqrt((a-1)^2 + b^2)        (a, b >= 1).

Deleting e only changes the contribution of the edges incident with u or v:

    Delta_e := SO(G) - SO(G-e)
             = sqrt(d_u^2+d_v^2)
               + sum_{x in N(u)\{v}} [ sqrt(d_u^2+d_x^2) - sqrt((d_u-1)^2+d_x^2) ]
               + sum_{y in N(v)\{u}} [ sqrt(d_v^2+d_y^2) - sqrt((d_v-1)^2+d_y^2) ]
             = sqrt(d_u^2+d_v^2) + sum_{x in N(u)\{v}} c(d_u,d_x) + sum_{y in N(v)\{u}} c(d_v,d_y).

Summing over all edges: every edge uv contributes sqrt(d_u^2+d_v^2) once (total
SO(G)), and every ordered incident pair (u,x) contributes c(d_u,d_x) once for
each edge at u other than ux, i.e. (d_u - 1) times.  Hence

    sum_e Delta_e = SO(G) + C(G),
    C(G) := sum_{u} (d_u - 1) * sum_{x in N(u)} c(d_u, d_x)
          = sum_{uv in E} [ (d_u-1) c(d_u,d_v) + (d_v-1) c(d_v,d_u) ],       (*)

and since sum_e Delta_e = m SO(G) - sum_e SO(G-e),

    sum_e SO(G-e) = (m-1) SO(G) - C(G).                                    (**)

Consequences.
  * The "linear scaling" identity  sum_e SO(G-e) = (m-1) SO(G)  -- the natural
    guess that the index scales with the number of edges, which appears in this
    project's task statement and is *not* a claim of the published literature
    (see refs/symmetry-2024-mapping.md) -- is *false* unless C(G) = 0, i.e.
    unless every edge has an endpoint of degree 1 (a matching; for connected
    graphs only K2).  Exhaustively: of the 288,249 graphs with m >= 2, n <= 9 it
    holds for exactly 12, and those 12 are precisely the matchings with at least
    two edges (results/naive_identity_characterization.json).
  * C(G) depends on G only through the multiset of *degree pairs* of its edges
    (its 'edge-type multiset').  Therefore (**) yields
        SO(G) = ( sum_e SO(G-e) + C(G) ) / (m-1),
    i.e. the Sombor index is recoverable from the edge deck as soon as the deck
    determines the edge-type multiset.
  * {Delta_e} and {SO(G-e)} carry the same numbers shifted by SO(G); because
    SO(G) is itself deck recoverable, the shift does not lose information, but
    the two multisets do *differ* as signatures, and we measure which is stronger.

Outputs
  results/sombor_identity_check.csv     per n: identity verification counts
  results/sombor_summary.json           headline numbers
  results/sombor_delta_by_type.csv      Delta_e statistics per edge degree type
  results/sombor_signature_power.csv    collision/ambiguity statistics of the
                                        Sombor-based signatures vs. targets
  results/sombor_correction_examples.json  graphs whose cards have equal SO but
                                        different Delta signature, etc.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import json
import math
import os
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import graphlib as gl
import invariants as inv
import dataset as ds

TOL = 1e-9


def c_fn(a: int, b: int) -> float:
    return math.sqrt(a * a + b * b) - math.sqrt((a - 1) ** 2 + b * b)


def correction_C(adj) -> float:
    """C(G) from (*) -- computed from the edge-type multiset only."""
    deg = gl.degrees(adj)
    tot = 0.0
    for u, v in gl.edges_of(adj):
        du, dv = deg[u], deg[v]
        if du >= 2:
            tot += (du - 1) * c_fn(du, dv)
        if dv >= 2:
            tot += (dv - 1) * c_fn(dv, du)
    return tot


def analyse_graph(g6: str) -> dict:
    adj = gl.from_graph6(g6)
    n = len(adj)
    m = gl.n_edges(adj)
    deg = gl.degrees(adj)
    so = inv.sombor(adj)
    sod = []
    dd = []
    edgetypes = []
    edge_deltas = []
    for u, v in gl.edges_of(adj):
        card = list(adj)
        card[u] &= ~(1 << v)
        card[v] &= ~(1 << u)
        so_card = inv.sombor(tuple(card))
        sod.append(so_card)
        dd.append(so - so_card)
        t = (min(deg[u], deg[v]), max(deg[u], deg[v]))
        edgetypes.append(t)
        edge_deltas.append((t, so - so_card))
    sod.sort()
    dd.sort()
    et = tuple(sorted(edgetypes))
    C = correction_C(adj)
    out = {
        "g6": g6,
        "n": n,
        "m": m,
        "so": so,
        "C": C,
        "sum_sod": sum(sod),
        "sum_dd": sum(dd),
        "naive_rhs": (m - 1) * so if m >= 1 else 0.0,
        "corr_rhs": (m - 1) * so - C if m >= 1 else 0.0,
        "sod": tuple(sod),
        "dd": tuple(dd),
        "et": et,
        "edge_deltas": edge_deltas,
        "ds": tuple(sorted(deg, reverse=True)),
    }
    return out


def qkey(vals):
    return tuple(inv.Q(x) for x in vals)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graphs", default="results/graphs.jsonl.gz")
    ap.add_argument("--limit", type=int, default=0, help="0 = all graphs")
    ap.add_argument("--sets", default="chem_n9,chemp_n9,chem_n8,conn_n8,all_n8,conn_n9,all_n9")
    args = ap.parse_args()

    meta = ds.load_graphs(args.graphs)
    order = sorted(meta.keys(), key=lambda g: (meta[g]["n"], g))
    if args.limit:
        order = order[: args.limit]
    print(f"analysing {len(order)} graphs", flush=True)

    rows = []
    naive_fail = Counter()
    corr_fail = Counter()
    et_to_C = defaultdict(set)          # edge-type multiset -> C values
    C_counterexample = []
    delta_by_type = defaultdict(list)   # (du,dv) -> list of Delta values
    delta_to_type = defaultdict(set)    # quantised Delta -> set of types
    type_to_delta_q = defaultdict(set)  # type -> set of quantised Delta
    records = []
    for i, g6 in enumerate(order):
        r = analyse_graph(g6)
        records.append(r)
        n, m, C = r["n"], r["m"], r["C"]
        if m >= 2:
            if abs(r["sum_sod"] - r["naive_rhs"]) > 1e-7:
                naive_fail[n] += 1
            if abs(r["sum_sod"] - r["corr_rhs"]) > 1e-7:
                corr_fail[n] += 1
        et_to_C[r["et"]].add(inv.Q(C))
        for (t, d) in r["edge_deltas"]:
            delta_by_type[t].append(d)
            q = inv.Q(d)
            delta_to_type[q].add(t)
            type_to_delta_q[t].add(q)
        if (i + 1) % 50000 == 0:
            print(f"  {i+1}/{len(order)}", flush=True)

    # ---- C depends only on the edge-type multiset -------------------------
    bad_C = {k: v for k, v in et_to_C.items() if len(v) > 1}
    print(f"edge-type multisets: {len(et_to_C)}, with >1 distinct C: {len(bad_C)}", flush=True)

    # ---- identity verification table --------------------------------------
    with open("results/sombor_identity_check.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["n", "graphs_with_m>=2", "naive_identity_failures",
                    "corrected_identity_failures", "max_rel_gap_naive", "min_C", "max_C"])
        for n in sorted({r["n"] for r in records}):
            sub = [r for r in records if r["n"] == n]
            sub2 = [r for r in sub if r["m"] >= 2]
            gaps = [abs(r["sum_sod"] - r["naive_rhs"]) / max(r["naive_rhs"], 1e-12) for r in sub2]
            Cs = [r["C"] for r in sub2]
            w.writerow([n, len(sub2), naive_fail.get(n, 0), corr_fail.get(n, 0),
                        f"{max(gaps) if gaps else 0:.6f}", f"{min(Cs) if Cs else 0:.6f}",
                        f"{max(Cs) if Cs else 0:.6f}"])
    # ---- Delta by edge type ------------------------------------------------
    with open("results/sombor_delta_by_type.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["d_u", "d_v", "n_edges", "n_distinct_delta", "delta_min", "delta_max",
                    "delta_mean", "n_distinct_types_sharing_a_delta"])
        types = sorted(delta_by_type)
        type_delta_sets = {t: set(inv.Q(x) for x in v) for t, v in delta_by_type.items()}
        for t in types:
            vals = delta_by_type[t]
            shared = sum(1 for q in type_delta_sets[t] if len(delta_to_type[q]) > 1)
            w.writerow([t[0], t[1], len(vals), len(type_delta_sets[t]),
                        f"{min(vals):.9f}", f"{max(vals):.9f}", f"{sum(vals)/len(vals):.9f}",
                        shared])

    # ---- signature power ---------------------------------------------------
    preds = ds.set_predicates()
    set_names = [s for s in args.sets.split(",") if s in preds]
    targets = ["ds", "et", "m", "n"]
    sig_power = []
    examples = {"so_equal_sod_differs": [], "delta_type_injectivity": []}
    for sname in set_names:
        pred = preds[sname]
        sub = [r for r in records if pred(meta[r["g6"]])]
        if not sub:
            continue
        sod_keys = [qkey(r["sod"]) for r in sub]
        dd_keys = [qkey(r["dd"]) for r in sub]
        for label, keys in [("S_SO", sod_keys), ("S_delta", dd_keys)]:
            st = ds.partition_stats(keys)
            row = {"set": sname, "signature": label, "n": st["n"], "classes": st["classes"],
                   "resolved": st["resolved"], "collision_graphs": st["collision_graphs"],
                   "largest_class": st["largest_class"], "residual_bits": st["residual_bits"]}
            for t in targets:
                tkeys = [r[t] for r in sub]
                row[f"determines_{t}"] = ds.determines(keys, tkeys)
            row["determines_SO(G)"] = ds.determines(keys, [inv.Q(r["so"]) for r in sub])
            sig_power.append(row)
            print(f"  {sname:10s} {label:8s} classes={st['classes']:7d} coll={st['collision_graphs']:7d} "
                  f"res_bits={st['residual_bits']:8.3f} det_SO={row['determines_SO(G)']} "
                  f"det_ds={row['determines_ds']} det_et={row['determines_et']}", flush=True)

        # graphs with identical {SO(G-e)} but different SO(G): the Delta signature
        # must separate them (it is the same multiset shifted by SO(G))
        groups = defaultdict(list)
        for r in sub:
            groups[qkey(r["sod"])].append(r)
        found = 0
        for k, members in groups.items():
            so_vals = {inv.Q(r["so"]) for r in members}
            if len(so_vals) > 1:
                found += 1
                if len(examples["so_equal_sod_differs"]) < 8:
                    members = sorted(members, key=lambda r: (r["n"], r["m"], r["g6"]))[:2]
                    examples["so_equal_sod_differs"].append({
                        "set": sname,
                        "graphs": [{"g6": r["g6"], "n": r["n"], "m": r["m"],
                                    "SO": round(r["so"], 9), "ds": list(r["ds"]),
                                    "et": [list(x) for x in r["et"]],
                                    "sod": [round(x, 9) for x in r["sod"]],
                                    "delta": [round(x, 9) for x in r["dd"]]} for r in members],
                    })
        print(f"  {sname}: {found} S_SO-classes contain >1 distinct SO(G)", flush=True)

    with open("results/sombor_signature_power.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(sig_power[0].keys()))
        w.writeheader()
        w.writerows(sig_power)

    # ---- does Delta determine the edge type? ------------------------------
    multi = {q: sorted(ts) for q, ts in delta_to_type.items() if len(ts) > 1}
    print(f"quantised Delta values seen: {len(delta_to_type)}, shared by >1 edge type: {len(multi)}",
          flush=True)
    for q, ts in sorted(multi.items())[:20]:
        examples["delta_type_injectivity"].append({"delta": q / 1e9, "types": ts})
    summary = {
        "n_graphs_analysed": len(records),
        "naive_identity_failures_total": sum(naive_fail.values()),
        "corrected_identity_failures_total": sum(corr_fail.values()),
        "edge_type_multisets": len(et_to_C),
        "edge_type_multisets_with_inconsistent_C": len(bad_C),
        "distinct_edge_types_seen": len(delta_by_type),
        "delta_values_total": sum(len(v) for v in delta_by_type.values()),
        "delta_values_shared_by_multiple_types": len(multi),
        "delta_is_injective_on_edge_types": len(multi) == 0,
        "delta_examples_shared": [
            {"delta": q / 1e9, "types": sorted(ts)} for q, ts in sorted(multi.items())[:10]
        ],
    }
    with open("results/sombor_summary.json", "w") as f:
        json.dump(summary, f, indent=1)
    with open("results/sombor_correction_examples.json", "w") as f:
        json.dump(examples, f, indent=1)
    print(json.dumps(summary, indent=1))
    print("wrote results/sombor_*.csv/json")


if __name__ == "__main__":
    main()
