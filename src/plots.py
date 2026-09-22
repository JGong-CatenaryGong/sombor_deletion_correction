"""
plots.py -- figures for the report.

  fig1_delta_by_type.png    Delta_e ranges per edge degree-type (chemical graphs)
  fig2_signature_power.png  residual ambiguity of every deck signature
  fig3_deck_vs_vertex.png   edge deck vs vertex deck: collision statistics
  fig4_examples.png         the smallest collision pairs, drawn
  fig5_sombor_correction.png  the falsified identity and the correction term
"""

from __future__ import annotations

import csv
import gzip
import json
import math
import os
import sys
from collections import defaultdict

os.environ.setdefault("MPLCONFIGDIR", os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), ".mplcache"))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import graphlib as gl
import invariants as inv
import dataset as ds

FIG = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "figures")
FLAG_CHEMICAL = 64


def _delta_of(adj, u, v, deg):
    a, b = deg[u], deg[v]
    d = math.sqrt(a * a + b * b)
    m = adj[u] & ~(1 << v)
    while m:
        bit = m & -m
        x = bit.bit_length() - 1
        m ^= bit
        d += math.sqrt(a * a + deg[x] ** 2) - math.sqrt((a - 1) ** 2 + deg[x] ** 2)
    m = adj[v] & ~(1 << u)
    while m:
        bit = m & -m
        y = bit.bit_length() - 1
        m ^= bit
        d += math.sqrt(b * b + deg[y] ** 2) - math.sqrt((b - 1) ** 2 + deg[y] ** 2)
    return d


def fig1_delta_by_type(graphs):
    meta = ds.load_graphs()
    per_type = defaultdict(list)
    n_chem = 0
    with gzip.open("results/graphs.jsonl.gz", "rt") as f:
        for line in f:
            r = json.loads(line)
            if not (r["fl"] & FLAG_CHEMICAL):
                continue
            n_chem += 1
            adj = gl.from_graph6(r["g6"])
            deg = gl.degrees(adj)
            for u, v in gl.edges_of(adj):
                t = tuple(sorted((deg[u], deg[v])))
                per_type[t].append(_delta_of(adj, u, v, deg))
    types = sorted(per_type)
    data = [per_type[t] for t in types]
    fig, ax = plt.subplots(figsize=(9, 5))
    bp = ax.boxplot(data, tick_labels=[f"{a}-{b}" for a, b in types], showfliers=False,
                    patch_artist=True, widths=0.6)
    for patch in bp["boxes"]:
        patch.set_facecolor("#cfe3f3")
    for i, t in enumerate(types):
        vals = per_type[t]
        ax.scatter([i + 1] * len(vals), vals, s=1.2, color="#1f4e79", alpha=0.25, zorder=3)
    ax.set_xlabel("edge degree-type $(d_u,d_v)$")
    ax.set_ylabel(r"$\Delta_e = SO(G)-SO(G-e)$")
    ax.set_title(f"Deletion increment by edge type -- chemical graphs (n<=9, {n_chem} graphs)")
    ax.grid(alpha=0.3, axis="y")
    fig.tight_layout()
    fig.savefig(os.path.join(FIG, "fig1_delta_by_type.png"), dpi=150)
    plt.close(fig)
    print("fig1 done", flush=True)
    return per_type


def fig2_signature_power():
    rows = list(csv.DictReader(open("results/invariant_collisions.csv")))
    for setname, fname in [("chem_n9", "fig2_signature_power.png"), ("conn_n9", "fig2_signature_power_conn9.png")]:
        sub = [r for r in rows if r["set"] == setname and r["source"].startswith("deck:")
               and r["source"] != "deck:itself"]
        sub.sort(key=lambda r: float(r["residual_bits"]))
        names = [r["source"].replace("deck:", "") for r in sub]
        bits = [float(r["residual_bits"]) for r in sub]
        ident = float(sub[0]["identity_bits"]) if sub else 0
        fig, ax = plt.subplots(figsize=(9, 8))
        colors = ["#2e7d32" if b <= 1e-9 else ("#f9a825" if b < 0.5 else "#c62828") for b in bits]
        ax.barh(range(len(names)), bits, color=colors)
        ax.set_yticks(range(len(names)))
        ax.set_yticklabels(names, fontsize=8)
        ax.axvline(ident, ls="--", color="k", lw=1, label=f"log2|S| = {ident:.2f} bits (no information)")
        ax.set_xlabel("residual ambiguity $H(G\\,|\\,S_I(G))$  [bits]")
        ax.set_title(f"Information retained by each edge-deck signature -- {setname}")
        ax.legend(fontsize=8)
        ax.grid(alpha=0.3, axis="x")
        fig.tight_layout()
        fig.savefig(os.path.join(FIG, fname), dpi=150)
        plt.close(fig)
    print("fig2 done", flush=True)


def _draw_pair(axes, g1, g2, title1, title2, caption):
    for ax, g6, ttl in ((axes[0], g1, title1), (axes[1], g2, title2)):
        adj = gl.from_graph6(g6)
        G = nx.Graph()
        G.add_nodes_from(range(len(adj)))
        G.add_edges_from(gl.edges_of(adj))
        pos = nx.spring_layout(G, seed=7)
        nx.draw_networkx(G, pos, ax=ax, node_size=200, node_color="#dbe9f6",
                         edgecolors="#204060", font_size=7, width=1.2)
        ax.set_title(ttl, fontsize=8)
        ax.axis("off")
    axes[0].text(-0.15, 1.22, caption, transform=axes[0].transAxes, fontsize=8, ha="left")


def fig4_examples():
    """The two headline collision pairs, drawn."""
    import invariants as inv
    fig, axes = plt.subplots(2, 2, figsize=(8.6, 8.4))
    # (a) minimal SO-deck collision in the range m >= 4
    stats = {}
    for g6 in ("EEj_", "EQjO"):
        adj = gl.from_graph6(g6)
        fp = inv.quantised_fingerprint(adj)
        stats[g6] = fp
    _draw_pair(
        axes[0], "EEj_", "EQjO",
        f"EEj_  tau={stats['EEj_']['taus']}, triangles={stats['EEj_']['tri']}, W={stats['EEj_']['wiener']/1e9:.0f}",
        f"EQjO  tau={stats['EQjO']['taus']}, triangles={stats['EQjO']['tri']}, W={stats['EQjO']['wiener']/1e9:.0f}",
        "(a) same Sombor deck, same edge-type deck, different spanning-tree count",
    )
    # (b) the classical m=3 exception that also defeats the SO deck
    _draw_pair(
        axes[1], "Bw", "CF",
        "Bw = C3, SO = 3*sqrt(8)",
        "CF = K1,3, SO = 3*sqrt(10)",
        "(b) {SO(G-e)} = {2*sqrt(5)}^3 for both; m = 3 (< 4)",
    )
    fig.suptitle("Collisions of the Sombor edge deck", fontsize=11)
    fig.tight_layout(rect=(0, 0, 1, 0.96))
    fig.savefig(os.path.join(FIG, "fig4_examples.png"), dpi=150)
    plt.close(fig)
    print("fig4 done", flush=True)


def fig5_correction():
    """Naive identity vs corrected identity on all graphs with m >= 2."""
    xs, ys, cs = [], [], []
    with gzip.open("results/graphs.jsonl.gz", "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["n"] > 7 or r["m"] < 2:
                continue
            adj = gl.from_graph6(r["g6"])
            deg = gl.degrees(adj)
            so = inv.sombor(adj)
            m = r["m"]
            s = 0.0
            for u, v in gl.edges_of(adj):
                c = list(adj)
                c[u] &= ~(1 << v)
                c[v] &= ~(1 << u)
                s += inv.sombor(tuple(c))
            C = 0.0
            for u, v in gl.edges_of(adj):
                a, b = deg[u], deg[v]
                if a >= 2:
                    C += (a - 1) * (math.sqrt(a * a + b * b) - math.sqrt((a - 1) ** 2 + b * b))
                if b >= 2:
                    C += (b - 1) * (math.sqrt(b * b + a * a) - math.sqrt((b - 1) ** 2 + a * a))
            xs.append((m - 1) * so)
            ys.append(s)
            cs.append(C / ((m - 1) * so) if (m - 1) * so else 0)
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.4))
    lim = max(xs) * 1.05
    axes[0].plot([0, lim], [0, lim], "k--", lw=1, label=r"$y=(m-1)SO(G)$ (claimed identity)")
    sc = axes[0].scatter(xs, ys, c=cs, s=14, cmap="viridis")
    axes[0].set_xlabel(r"$(m-1)\,SO(G)$")
    axes[0].set_ylabel(r"$\sum_e SO(G-e)$")
    axes[0].set_title("Claimed identity fails for every graph with $m\\geq2$")
    axes[0].legend(fontsize=8)
    axes[0].grid(alpha=0.3)
    fig.colorbar(sc, ax=axes[0], label=r"$C(G)/((m-1)SO(G))$")
    axes[1].hist(cs, bins=60, color="#1f4e79")
    axes[1].set_xlabel(r"relative correction $C(G)/((m-1)SO(G))$")
    axes[1].set_ylabel("graphs")
    axes[1].set_title(r"size of the correction term $C(G)$")
    axes[1].grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(FIG, "fig5_sombor_correction.png"), dpi=150)
    plt.close(fig)
    print("fig5 done", flush=True)


def main():
    os.makedirs(FIG, exist_ok=True)
    fig1_delta_by_type(None)
    fig2_signature_power()
    fig5_correction()
    fig4_examples()


if __name__ == "__main__":
    main()
