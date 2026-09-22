"""
dataset.py -- shared loading utilities and set definitions for the analyses.

Analysis sets (used consistently in every table of the report):
  all_n8       every graph with n <= 8
  conn_n8      connected graphs with n <= 8
  chem_n8      chemical graphs (connected, max degree <= 4) with n <= 8
  chemp_n8     chemical and planar, n <= 8
  all_n9       every graph with n <= 9
  conn_n9      connected graphs with n <= 9
  chem_n9      chemical graphs with n <= 9
  chemp_n9     chemical and planar, n <= 9
  chem_m4_n9   chemical graphs with n <= 9 and m >= 4 (ERC range)
"""

from __future__ import annotations

import gzip
import json
import math
import os
from collections import defaultdict

FLAG_CONNECTED = 1
FLAG_PLANAR = 2
FLAG_BICONN = 4
FLAG_BIPARTITE = 8
FLAG_FOREST = 16
FLAG_TREE = 32
FLAG_CHEMICAL = 64
FLAG_CHEM_PLANAR = 128
FLAG_MGE4 = 256

RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")


def load_graphs(path: str | None = None) -> dict[str, dict]:
    path = path or os.path.join(RESULTS, "graphs.jsonl.gz")
    out = {}
    with gzip.open(path, "rt") as f:
        for line in f:
            r = json.loads(line)
            out[r["g6"]] = r
    return out


def load_decks(kind: str = "edge", path: str | None = None) -> list[dict]:
    path = path or os.path.join(RESULTS, f"deck_{kind}.jsonl.gz")
    out = []
    with gzip.open(path, "rt") as f:
        for line in f:
            out.append(json.loads(line))
    return out


def load_invariant_names() -> list[str]:
    import sys
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
    import invariants as inv
    return list(inv.INVARIANTS)


def set_predicates():
    return {
        "all_n8": lambda r: r["n"] <= 8,
        "conn_n8": lambda r: r["n"] <= 8 and (r["fl"] & FLAG_CONNECTED),
        "chem_n8": lambda r: r["n"] <= 8 and (r["fl"] & FLAG_CHEMICAL),
        "chemp_n8": lambda r: r["n"] <= 8 and (r["fl"] & FLAG_CHEM_PLANAR),
        "all_n9": lambda r: True,
        "conn_n9": lambda r: bool(r["fl"] & FLAG_CONNECTED),
        "chem_n9": lambda r: bool(r["fl"] & FLAG_CHEMICAL),
        "chemp_n9": lambda r: bool(r["fl"] & FLAG_CHEM_PLANAR),
        "chem_m4_n9": lambda r: bool(r["fl"] & FLAG_CHEMICAL) and bool(r["fl"] & FLAG_MGE4),
        "conn_m4_n9": lambda r: bool(r["fl"] & FLAG_CONNECTED) and bool(r["fl"] & FLAG_MGE4),
    }


# --------------------------------------------------------------------------
# partition statistics
# --------------------------------------------------------------------------
def partition_stats(keys: list) -> dict:
    """Statistics of the partition induced by a signature key per graph."""
    n = len(keys)
    groups: dict = defaultdict(list)
    for i, k in enumerate(keys):
        groups[k].append(i)
    sizes = [len(v) for v in groups.values()]
    n_classes = len(groups)
    colliding = sum(s for s in sizes if s > 1)
    largest = max(sizes) if sizes else 0
    residual_bits = 0.0
    for s in sizes:
        if s > 1:
            residual_bits += (s / n) * math.log2(s)
    return {
        "n": n,
        "classes": n_classes,
        "resolved": n_classes == n,
        "collision_graphs": colliding,
        "collision_rate": colliding / n if n else 0.0,
        "largest_class": largest,
        "residual_bits": residual_bits,
        "identity_bits": math.log2(n) if n else 0.0,
        "groups": groups,
    }


def entropy(counts) -> float:
    tot = sum(counts)
    if tot <= 0:
        return 0.0
    h = 0.0
    for c in counts:
        if c:
            p = c / tot
            h -= p * math.log2(p)
    return h


def mutual_information(keys_a: list, keys_b: list) -> tuple[float, float]:
    """(I(A;B), H(B|A)) in bits for two signature partitions of the same set."""
    joint: dict = defaultdict(int)
    ca: dict = defaultdict(int)
    cb: dict = defaultdict(int)
    for a, b in zip(keys_a, keys_b):
        joint[(a, b)] += 1
        ca[a] += 1
        cb[b] += 1
    n = len(keys_a)
    h_a = entropy(ca.values())
    h_b = entropy(cb.values())
    h_ab = entropy(joint.values())
    mi = h_a + h_b - h_ab
    h_b_given_a = h_ab - h_a
    return mi, h_b_given_a


def determines(keys_sig: list, keys_target: list) -> bool:
    """True iff the signature S determines the target T (T constant on S-classes)."""
    seen: dict = {}
    for s, t in zip(keys_sig, keys_target):
        prev = seen.get(s)
        if prev is None:
            seen[s] = t
        elif prev != t:
            return False
    return True
