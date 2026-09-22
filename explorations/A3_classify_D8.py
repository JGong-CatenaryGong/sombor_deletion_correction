"""
A3 D=8: complete classification of exact Delta coincidences for degrees <= 8.

Exactness scheme (sound quantisation):
  * pass 1 buckets configurations by the *rounded float value* of Delta
    (round to 1e-6; equal algebraic values can differ by ~1e-15 in floating
    point, so they always share a bucket);
  * pass 2 re-enumerates and, for every flagged bucket only, recomputes the
    EXACT integer coordinate vector over the multiquadratic basis
    {sqrt(s) : s squarefree} and groups exactly.
  So the classification is exact; the float pass is only a filter.

Reported: number of configurations, cross-type exact coincidence groups (the
phenomenon of interest: same Delta from different unordered degree types),
within-type collision counts, and the diagonal-union theorem at degree 8.
"""
import os
import sys
import json
import time
from collections import Counter, defaultdict
from itertools import combinations_with_replacement

HERE = os.path.dirname(os.path.abspath(__file__))
D = 8
W = 12
SCALE = 10 ** 6


def squarefree_part(N):
    g, d, n = 1, 2, N
    while d * d <= n:
        while n % (d * d) == 0:
            n //= d * d
            g *= d
        d += 1
    return n, g


def build_basis(D):
    parts = set()
    for a in range(1, D + 1):
        for b in range(1, D + 1):
            for N in (a * a + b * b, (a - 1) ** 2 + b * b, (b - 1) ** 2 + a * a):
                if N > 0:
                    parts.add(squarefree_part(N)[0])
    basis = sorted(parts)
    return basis, {s: i for i, s in enumerate(basis)}


import math


def vec_of(N, idx):
    s, g = squarefree_part(N)
    return {idx[s]: g}


def vadd(a, b):
    o = dict(a)
    for k, v in b.items():
        o[k] = o.get(k, 0) + v
        if o[k] == 0:
            del o[k]
    return o


def pack(vec):
    p = n = 0
    for k, v in vec.items():
        if v > 0:
            p += v << (W * k)
        elif v < 0:
            n += (-v) << (W * k)
    return p, n


def unpack(pos, neg, nb):
    mask = (1 << W) - 1
    return tuple(((pos >> (W * k)) & mask) - ((neg >> (W * k)) & mask) for k in range(nb))


def c_vec(a, x, idx):
    v = vadd(vec_of(a * a + x * x, idx),
             {k: -t for k, t in vec_of((a - 1) ** 2 + x * x, idx).items()})
    return v


def c_float(a, x):
    return math.sqrt(a * a + x * x) - math.sqrt((a - 1) ** 2 + x * x)


def main():
    t0 = time.perf_counter()
    basis, idx = build_basis(D)
    nb = len(idx)
    print(f"D={D}: {nb} basis radicals {basis}", flush=True)

    sides = {}
    for a in range(1, D + 1):
        lst = []
        for A in combinations_with_replacement(range(1, D + 1), a - 1):
            v = {}
            f = 0.0
            for x in A:
                v = vadd(v, c_vec(a, x, idx))
                f += c_float(a, x)
            lst.append((A, pack(v), f))
        sides[a] = lst
    total_sides = sum(len(v) for v in sides.values())
    print(f"sides: {total_sides}", flush=True)

    types = [(a, b) for a in range(1, D + 1) for b in range(a, D + 1)]
    type_bit = {t: i for i, t in enumerate(types)}
    base_pack, base_float = {}, {}
    for (a, b) in types:
        base_pack[(a, b)] = pack(vec_of(a * a + b * b, idx))
        base_float[(a, b)] = math.sqrt(a * a + b * b)

    # ---------- pass 1: float buckets ----------
    buckets = {}
    n_cfg = 0
    for (a, b) in types:
        bf = base_float[(a, b)]
        bit = 1 << type_bit[(a, b)]
        la, lb = sides[a], sides[b]
        if a == b:
            rng = ((i, j) for i in range(len(la)) for j in range(i, len(la)))
        else:
            rng = ((i, j) for i in range(len(la)) for j in range(len(lb)))
        for i, j in rng:
            key = int(round((bf + la[i][2] + lb[j][2]) * SCALE))
            cur = buckets.get(key)
            if cur is None:
                buckets[key] = (1 << 36) | bit
            else:
                cnt = cur >> 36
                buckets[key] = (min(cnt + 1, 63) << 36) | (cur & ((1 << 36) - 1)) | bit
            n_cfg += 1
    flagged = {k for k, v in buckets.items()
               if (v >> 36) >= 2 or bin(v & ((1 << 36) - 1)).count("1") >= 2}
    print(f"pass 1: {n_cfg} configs, {len(buckets)} float buckets, "
          f"{len(flagged)} flagged [{time.perf_counter()-t0:.1f}s]", flush=True)

    # ---------- pass 2: exact keys inside flagged buckets ----------
    exact = {}
    union_of = defaultdict(set)          # exact key -> set of unions (diagonal types)
    union_key = defaultdict(set)         # union -> set of exact keys
    for (a, b) in types:
        bf = base_float[(a, b)]
        bp, bn = base_pack[(a, b)]
        la, lb = sides[a], sides[b]
        if a == b:
            rng = ((i, j) for i in range(len(la)) for j in range(i, len(la)))
        else:
            rng = ((i, j) for i in range(len(la)) for j in range(len(lb)))
        for i, j in rng:
            if int(round((bf + la[i][2] + lb[j][2]) * SCALE)) not in flagged:
                continue
            pa, na = la[i][1]
            pb2, nb2 = lb[j][1]
            key = unpack(bp + pa + pb2, bn + na + nb2, nb)
            rec = exact.get(key)
            if rec is None:
                exact[key] = {"count": 1, "types": {(a, b)},
                              "example": (a, b, list(la[i][0]), list(lb[j][0])),
                              "float": bf + la[i][2] + lb[j][2]}
            else:
                rec["count"] += 1
                rec["types"].add((a, b))
            if a == b:
                u = (a, tuple(sorted(la[i][0] + lb[j][0])))
                union_of[key].add(u)
                union_key[u].add(key)
    cross = {k: v for k, v in exact.items() if len(v["types"]) >= 2}
    within = {k: v for k, v in exact.items() if len(v["types"]) == 1 and v["count"] >= 2}
    # diagonal-union injectivity: a union must determine the value
    noninj = {u: ks for u, ks in union_key.items() if len(ks) >= 2}
    diag = {}
    for a in range(1, D + 1):
        u_a = [u for u in union_key if u[0] == a]
        k_a = set()
        for u in u_a:
            k_a |= union_key[u]
        diag[a] = {"n_unions": len(u_a), "n_values": len(k_a), "injective": len(u_a) == len(k_a)}
    print(f"pass 2: exact keys {len(exact)}, cross-type groups {len(cross)}, "
          f"within-type groups {len(within)} [{time.perf_counter()-t0:.1f}s]", flush=True)

    out = {
        "script": "explorations/A3_classify_D8.py",
        "D": D, "basis": basis, "n_basis": nb, "n_sides": total_sides,
        "n_configurations": n_cfg, "n_float_buckets": len(buckets),
        "n_flagged_buckets": len(flagged),
        "n_exact_keys_in_flagged": len(exact),
        "n_cross_type_groups": len(cross),
        "cross_type_groups": [
            {"example": v["example"], "types": sorted(v["types"]), "count": v["count"],
             "float": v["float"]} for v in list(cross.values())[:20]],
        "n_within_type_groups": len(within),
        "within_type_examples": [
            {"example": v["example"], "count": v["count"]} for v in list(within.values())[:5]],
        "diagonal_union": diag,
        "diagonal_union_counterexamples": [
            {"union": [u[0], list(u[1])], "keys": len(ks)}
            for u, ks in list(noninj.items())[:5]],
        "runtime_s": time.perf_counter() - t0,
    }
    with open(os.path.join(HERE, "results", "A3_classification_D8.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: out[k] for k in ("n_configurations", "n_flagged_buckets",
                                          "n_cross_type_groups", "n_within_type_groups",
                                          "diagonal_union")}, indent=1))
    print("cross-type groups:", json.dumps(out["cross_type_groups"], indent=1))
    print("wrote explorations/results/A3_classification_D8.json")


if __name__ == "__main__":
    main()
