"""
audit_inequalities.py -- audit EVERY inequality stated in the report, in the
direction in which it is stated, after the monotonicity-direction error was found.

For each graph (exhaustively for n <= 9, plus large random/structured graphs) we
compute the residual of each claim in its *stated* direction and count violations.
The falsified conjecture is included as R0 so that its failure is documented
rather than hidden.

Claims audited (as they now appear in report.md)
  R0 (FALSIFIED, no longer used)
        sum_u d_u(d_u-1) c(d_u,1)  <=  C(G)                [was conjectured as a lower bound]
  R1  C(G) <= m(m-1) c(m,1)                                 [star theorem]
  R2  C(G) <= (M1 - 2m) c(m,1)                              [intermediate bound]
  R3  C(G) <= sum_u d_u(d_u-1) c(d_u,1)                     [degree-sequence upper bound]
  R4  sum_uv Psi_uv/(2d_u+2d_v-1) <= C(G)                   [sharp lower bound]
  R5  C(G) <= sqrt2 * sum_uv Psi_uv/(2d_u+2d_v-1)           [sharp upper bound]
  R6  Z/(4 Delta - 1) <= C(G) <= (sqrt2/3) Z                [Zagreb/Forgotten sandwich]
  R7  C(G) >= sum_u d_u(d_u-1) c(d_u,Delta)                 [lower bound via max degree]
  R8  C(G) >= (M1-m)(M1-2m)/(m(4 Delta-1))                  [pure M1 lower bound]
  R9  C(G) = 0  <=>  G is a matching
  R10 sum_e SO(G-e) = (m-1) SO(G) - C(G)                     [identity]
  R11 sum_e T_f(G-e) = (m-1) T_f(G) - C_f(G)  for f = Sombor, Randic, ABC, M2
  R12 C(G) <= (sqrt2/3) * [k z(n-1) + z(r)]  with 2m = k(n-1)+r, z(d)=d(d-1)(2d-1)

Identity residuals (R10, R11) are recorded as *relative* residuals, since the
absolute round-off of a sum of ~1e5 square roots is ~1e-8 while the relative error
is ~1e-13; a violation there means a relative residual above 1e-9.

Output: results/inequality_audit.json  (+ console table)
"""

from __future__ import annotations

import json
import math
import os
import random
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))

import graphlib as gl

RNG = random.Random(20240920)


def c_fn(a, b):
    return math.sqrt(a * a + b * b) - math.sqrt((a - 1) ** 2 + b * b)


def phi(a, b):
    return (a - 1) * c_fn(a, b) + (b - 1) * c_fn(b, a)


def sombor(adj):
    d = gl.degrees(adj)
    return sum(math.sqrt(d[u] ** 2 + d[v] ** 2) for u, v in gl.edges_of(adj))


def residuals(adj):
    """All residuals, in the direction in which the report states the claim: a
    residual < 0 means the stated claim fails."""
    d = gl.degrees(adj)
    n, m = len(adj), gl.n_edges(adj)
    out = {}
    if m < 2:
        return out
    C = sum(phi(d[u], d[v]) for u, v in gl.edges_of(adj))
    M1 = sum(x * x for x in d)
    F = sum(x ** 3 for x in d)
    Z = 2 * F - 3 * M1 + 2 * m
    D = max(d)
    cm1 = c_fn(m, 1)
    psi_sum = sum(((d[u] - 1) * (2 * d[u] - 1) + (d[v] - 1) * (2 * d[v] - 1))
                  / (2 * d[u] + 2 * d[v] - 1) for u, v in gl.edges_of(adj))
    L = sum(x * (x - 1) * c_fn(x, 1) for x in d)

    # R0: the falsified conjecture  L <= C  -> residual L - C, must be <= 0 to hold
    out["R0_falsified_L_le_C"] = L - C
    # R1..R3: upper bounds  -> bound - C >= 0
    out["R1_C_le_star"] = m * (m - 1) * cm1 - C
    out["R2_C_le_M1"] = (M1 - 2 * m) * cm1 - C
    out["R3_C_le_degseq"] = L - C
    # R4,R5 sharp sandwich
    out["R4_psi_le_C"] = C - psi_sum
    out["R5_C_le_sqrt2psi"] = math.sqrt(2) * psi_sum - C
    # R6 Zagreb/Forgotten sandwich
    out["R6a_Z_over_4D_le_C"] = C - Z / (4 * D - 1)
    out["R6b_C_le_sqrt2_3_Z"] = math.sqrt(2) / 3 * Z - C
    # R7,R8 lower bounds
    out["R7_C_ge_degseq_Delta"] = C - sum(x * (x - 1) * c_fn(x, D) for x in d)
    out["R8_C_ge_M1_bound"] = C - (M1 - m) * (M1 - 2 * m) / (m * (4 * D - 1))
    # R9 zero characterisation (1 = holds)
    out["R9_C0_iff_matching"] = int((C < 1e-12) == (max(d) <= 1))
    # R12 explicit (n,m) bound
    if n >= 2:
        k, r = divmod(2 * m, n - 1) if n > 1 else (0, 0)
        z = lambda x: x * (x - 1) * (2 * x - 1)
        out["R12_C_le_explicit_nm"] = math.sqrt(2) / 3 * (k * z(n - 1) + z(r)) - C
    # R10, R11 identities -> |residual| ~ 0
    if m <= 400:
        sSO = 0.0
        for u, v in gl.edges_of(adj):
            cc = list(adj)
            cc[u] &= ~(1 << v)
            cc[v] &= ~(1 << u)
            sSO += sombor(tuple(cc))
        _rhs = (m - 1) * sombor(adj) - C
        out["R10_sombor_identity"] = -abs(sSO - _rhs) / (1.0 + abs(_rhs))   # relative
        for name, f in [("randic", lambda a, b: 1 / math.sqrt(a * b)),
                        ("abc", lambda a, b: math.sqrt((a + b - 2) / (a * b)) if a + b > 2 else 0.0),
                        ("m2", lambda a, b: float(a * b))]:
            T = sum(f(d[u], d[v]) for u, v in gl.edges_of(adj))
            s = 0.0
            for u, v in gl.edges_of(adj):
                cc = list(adj)
                cc[u] &= ~(1 << v)
                cc[v] &= ~(1 << u)
                d2 = gl.degrees(tuple(cc))
                s += sum(f(d2[x], d2[y]) for x, y in gl.edges_of(tuple(cc)))
            Cf = 0.0
            for u, v in gl.edges_of(adj):
                if d[u] >= 2:
                    Cf += (d[u] - 1) * (f(d[u], d[v]) - f(d[u] - 1, d[v]))
                if d[v] >= 2:
                    Cf += (d[v] - 1) * (f(d[v], d[u]) - f(d[v] - 1, d[u]))
            _rhs = (m - 1) * T - Cf
            out[f"R11_{name}_identity"] = -abs(s - _rhs) / (1.0 + abs(_rhs))  # relative
    return out


def main():
    # exhaustive part: all graphs with n <= 9
    stats = {}
    fails = []
    with open("results/graphs.jsonl.gz", "rt") as f:
        import gzip
        pass
    import gzip
    with gzip.open("results/graphs.jsonl.gz", "rt") as f:
        for line in f:
            r = json.loads(line)
            adj = gl.from_graph6(r["g6"])
            for k, v in residuals(adj).items():
                st = stats.setdefault(k, {"n": 0, "min_margin": float("inf"), "viol": 0,
                                          "worst": None})
                st["n"] += 1
                margin = v if k.startswith(("R0", "R10", "R11")) else v
                if margin < st["min_margin"]:
                    st["min_margin"] = margin
                    st["worst"] = f"{r['g6']}(n={r['n']},m={r['m']})"
                bad = (v > 1e-9) if k.startswith("R0") else (
                    (v < -1e-9) if not k.startswith("R9") else (v != 1))
                if bad:
                    st["viol"] += 1
                    if len(fails) < 20:
                        fails.append({"claim": k, "graph": r["g6"], "n": r["n"],
                                      "m": r["m"], "residual": v})
    # large random part
    big = []
    for n, p in [(50, 0.1), (100, 0.05), (150, 0.3), (300, 0.02), (200, 0.9)]:
        big.append((f"G({n},{p})", nx.gnp_random_graph(n, p, seed=RNG.randrange(10 ** 6))))
    for n, r_ in [(40, 3), (80, 4), (150, 2)]:
        big.append((f"reg({n},{r_})", nx.random_regular_graph(r_, n, seed=RNG.randrange(10 ** 6))))
    for n in (60, 200):
        big.append((f"star(n={n})", nx.star_graph(n - 1)))
        big.append((f"path(n={n})", nx.path_graph(n)))
    big_stats = {}
    for name, G in big:
        adj = tuple(int("".join("1" if G.has_edge(i, j) else "0" for j in range(len(G)))
                        [::-1], 2) if False else 0 for i in range(len(G)))
        adj = []
        for i in range(len(G)):
            m_ = 0
            for j in G.neighbors(i):
                m_ |= 1 << j
            adj.append(m_)
        for k, v in residuals(tuple(adj)).items():
            st = big_stats.setdefault(k, {"min_margin": float("inf"), "viol": 0, "worst": None})
            if v < st["min_margin"]:
                st["min_margin"] = v
                st["worst"] = name
            bad = (v > 1e-9) if k.startswith("R0") else (
                (v < -1e-9) if not k.startswith("R9") else (v != 1))
            if bad:
                st["viol"] += 1
    summary = {
        "exhaustive_n_le_9": {k: {"graphs": v["n"], "violations": v["viol"],
                                  "min_margin": v["min_margin"], "at": v["worst"]}
                              for k, v in sorted(stats.items())},
        "large_graphs": {k: {"violations": v["viol"], "min_margin": v["min_margin"],
                             "at": v["worst"]} for k, v in sorted(big_stats.items())},
        "first_failures": fails,
    }
    with open("results/inequality_audit.json", "w") as f:
        json.dump(summary, f, indent=1)
    print(f"{'claim':32s} {'graphs':>8s} {'violations':>11s} {'min margin':>14s}  worst case")
    for k, v in sorted(stats.items()):
        print(f"{k:32s} {v['n']:8d} {v['viol']:11d} {v['min_margin']:14.6f}  {v['worst']}")
    print("\nlarge graphs:")
    for k, v in sorted(big_stats.items()):
        print(f"{k:32s} {'-':>8s} {v['viol']:11d} {v['min_margin']:14.6f}  {v['worst']}")


if __name__ == "__main__":
    main()
