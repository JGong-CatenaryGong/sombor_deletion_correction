"""
A3 -- exact classification of Delta coincidences via multiquadratic normal forms.

Delta(a,b,A,B) = sqrt(a^2+b^2) + sum_{x in A} c(a,x) + sum_{y in B} c(b,y),
c(p,q) = sqrt(p^2+q^2) - sqrt((p-1)^2+q^2).

Every square root occurring is sqrt(N) with N = p^2+q^2 <= 2*D^2, and
sqrt(N) = g*sqrt(s) with s squarefree and g integer.  The set
{sqrt(s) : s squarefree} is linearly independent over Q (basis of the
multiquadratic extension), so Delta is represented EXACTLY by its integer
coordinate vector over that basis, and

    Delta_1 = Delta_2  <=>  coordinate vectors equal.

No floating point, no precision threshold: this upgrades the 30-digit + sympy
audit of report section 7.4 to a complete decision procedure.

Part A: all 119,794 configurations occurring in the frozen n<=9 dataset
        (results/delta_configurations.csv, read-only).  Expected: exactly the
        two known cross-type families (sqrt(20): types (2,2)/(1,3);
        sqrt(52): types (3,3)/(2,4)), all other coincidences trivial
        ((a,b,A,B) vs (b,a,B,A)); the (2,8)/(4,7) near-miss must have
        DIFFERENT vectors.
Part B: complete bounded classification for degrees <= 7: every combinatorially
        possible configuration (a,b <= 7, |A| = a-1, |B| = b-1, entries <= 7),
        1714*1714 = 2,937,796 configurations -- the full list of cross-type
        coincidences (including identities NOT realized by any n<=9 graph),
        plus within-type coincidences (Delta is not injective in (A,B) even
        for fixed type).

Output: explorations/results/A3_classification.json
"""
import os
import sys
import csv
import json
import itertools
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def sqfree_split(n):
    """n = g^2 * s with s squarefree; returns (g, s)."""
    if n == 0:
        return (0, 1)
    g = 1
    p = 2
    while p * p <= n:
        while n % (p * p) == 0:
            n //= p * p
            g *= p
        p += 1
    return (g, n)


class Basis:
    def __init__(self, D):
        vals = set()
        for p in range(0, D + 1):
            for q in range(1, D + 1):
                vals.add(p * p + q * q)
        sq = sorted({sqfree_split(v)[1] for v in vals})
        self.idx = {s: i for i, s in enumerate(sq)}
        self.sq = sq
        self.dim = len(sq)
        self._cache = {}

    def vec_sqrt(self, n):
        v = self._cache.get(n)
        if v is None:
            g, s = sqfree_split(n)
            v = [0] * self.dim
            if g:
                v[self.idx[s]] = g
            v = tuple(v)
            self._cache[n] = v
        return v


def add(v1, v2):
    return tuple(a + b for a, b in zip(v1, v2))


def sub(v1, v2):
    return tuple(a - b for a, b in zip(v1, v2))


def vec_str(basis, v):
    terms = []
    for s, c in zip(basis.sq, v):
        if c == 0:
            continue
        terms.append(f"{c}" if s == 1 else (f"{c}*sqrt({s})" if c != 1 else f"sqrt({s})"))
    return " + ".join(terms) if terms else "0"


def build_cvecs(basis, D):
    cv = {}
    for a in range(1, D + 1):
        for x in range(1, D + 1):
            cv[(a, x)] = sub(basis.vec_sqrt(a * a + x * x),
                             basis.vec_sqrt((a - 1) ** 2 + x * x))
    return cv


def side_table(basis, cv, D):
    """All (a, A-tuple, gvec) with gvec = sum_{x in A} c(a,x)."""
    sides = []
    for a in range(1, D + 1):
        zero = tuple([0] * basis.dim)
        for A in itertools.combinations_with_replacement(range(1, D + 1), a - 1):
            g = zero
            for x in A:
                g = add(g, cv[(a, x)])
            sides.append((a, A, g))
    return sides


def delta_vec(basis, cv, a, b, A, B):
    v = basis.vec_sqrt(a * a + b * b)
    for x in A:
        v = add(v, cv[(a, x)])
    for y in B:
        v = add(v, cv[(b, y)])
    return v


def main():
    out = {"script": "explorations/A3_classify.py"}

    # ---------------- Part A: dataset configurations -----------------------
    D_A = 8
    basisA = Basis(D_A)
    cvA = build_cvecs(basisA, D_A)
    groups = {}
    n_rows = 0
    with open(os.path.join(ROOT, "results", "delta_configurations.csv")) as f:
        for row in csv.DictReader(f):
            n_rows += 1
            a = int(row["a"])
            b = int(row["b"])
            A = tuple(int(t) for t in row["A"].split(";") if t)
            B = tuple(int(t) for t in row["B"].split(";") if t)
            v = delta_vec(basisA, cvA, a, b, A, B)
            g = groups.get(v)
            if g is None:
                g = groups[v] = {"types": Counter(), "occurrences": Counter(),
                                 "n_configs": 0, "examples": []}
            t = (min(a, b), max(a, b))
            g["types"][t] += 1
            g["occurrences"][t] += int(row["count"])
            g["n_configs"] += 1
            if len(g["examples"]) < 6:
                g["examples"].append([a, b, list(A), list(B)])
    cross = []
    for v, g in groups.items():
        if len(g["types"]) >= 2:
            cross.append({"delta": vec_str(basisA, v),
                          "types": sorted(g["types"]),
                          "occurrences": {str(k): g["occurrences"][k] for k in g["types"]},
                          "n_configs": g["n_configs"],
                          "examples": g["examples"]})
    # the (2,8)/(4,7) near-miss must be distinct
    v1 = delta_vec(basisA, cvA, 2, 8, (5,), (2, 3, 3, 4, 4, 5, 5))
    v2 = delta_vec(basisA, cvA, 4, 7, (4, 5, 6), (3, 3, 3, 4, 6, 7))
    out["part_A_dataset"] = {
        "n_configurations": n_rows,
        "n_distinct_delta_values": len(groups),
        "n_cross_type_groups": len(cross),
        "cross_type_groups": cross,
        "near_miss_2_8_vs_4_7_vectors_differ": v1 != v2,
        "near_miss_vectors": {"(2,8;(5),(2,3,3,4,4,5,5))": vec_str(basisA, v1),
                              "(4,7;(4,5,6),(3,3,3,4,6,7))": vec_str(basisA, v2)},
    }
    print(f"Part A: {n_rows} configs -> {len(groups)} distinct Delta values, "
          f"{len(cross)} cross-type groups", flush=True)
    for c in cross:
        print("   ", c["delta"], c["types"], c["occurrences"], flush=True)

    # ---------------- Part B: complete bounded classification D=7 -----------
    D_B = 7
    basisB = Basis(D_B)
    cvB = build_cvecs(basisB, D_B)
    sides = side_table(basisB, cvB, D_B)
    n_pairs = len(sides) * (len(sides) + 1) // 2
    print(f"Part B: {len(sides)} sides -> {n_pairs} unordered configurations "
          f"(= {len(sides)**2} ordered)", flush=True)
    groupsB = defaultdict(lambda: [Counter(), 0, []])   # vec -> [types, ncfg, examples]
    for i in range(len(sides)):
        a1, A1, g1 = sides[i]
        for j in range(i, len(sides)):
            a2, A2, g2 = sides[j]
            v = add(add(basisB.vec_sqrt(a1 * a1 + a2 * a2), g1), g2)
            ent = groupsB[v]
            t = (min(a1, a2), max(a1, a2))
            ent[0][t] += 1
            ent[1] += 1
            if len(ent[2]) < 6:
                ent[2].append([a1, a2, list(A1), list(A2)])
    crossB = []
    within_type_multi = 0     # vectors with >=2 distinct configs (mod swap), one type
    for v, (types, ncfg, ex) in groupsB.items():
        if len(types) >= 2:
            crossB.append({"delta": vec_str(basisB, v),
                           "types": sorted(types),
                           "configs_per_type": {str(k): types[k] for k in sorted(types)},
                           "n_configs": ncfg,
                           "examples": ex})
        elif ncfg >= 2:
            within_type_multi += 1
    crossB.sort(key=lambda c: c["delta"])
    out["part_B_bounded_D7"] = {
        "D": D_B,
        "n_sides": len(sides),
        "n_configurations_unordered": n_pairs,
        "n_configurations_ordered": len(sides) ** 2,
        "n_distinct_delta_values": len(groupsB),
        "n_cross_type_groups": len(crossB),
        "cross_type_groups": crossB[:80],          # full list may be long; cap display
        "cross_type_group_count_total": len(crossB),
        "n_vectors_with_within_type_coincidences": within_type_multi,
    }
    print(f"Part B: {n_pairs} configs -> {len(groupsB)} distinct values, "
          f"{len(crossB)} cross-type groups, {within_type_multi} within-type "
          f"coincidence vectors", flush=True)
    for c in crossB[:12]:
        print("   ", c["delta"], c["types"], c["configs_per_type"], flush=True)

    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    with open(os.path.join(HERE, "results", "A3_classification.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("wrote explorations/results/A3_classification.json")


if __name__ == "__main__":
    main()
