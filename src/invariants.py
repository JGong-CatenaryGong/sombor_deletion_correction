r"""
invariants.py -- graph invariants computed on a single graph.

Every invariant is a pure function of the *isomorphism class*: it never depends
on the vertex labelling.  That is essential here, because the whole study
consists in comparing graphs through unlabelled "cards" G - e.

Floating point invariants (Sombor, Wiener, spectra, ...) are irrational in
general.  For hashing/grouping they are quantised with ``Q(x) = round(x*1e9)``.
Floating-point invariants are compared after the canonical quantisation
$Q(x) = \mathrm{round}(10^9 x)$ (integers and tuples are used as they are).
There is *no* automatic monitoring of the gap between different values: a
measured check (see the review notes in report.md section 1.4) shows that the
smallest gap between two distinct values of `energy`, `spectral_radius`,
`randic`, `abc` and `sombor_inv` is of the order of the machine epsilon
(~1e-16), i.e. it is *not* far above the quantum.  Those minimal gaps occur
between values that are mathematically equal (equienergetic / equi-Randic
coincidences computed with different rounding), so merging them loses nothing,
but in general a quantised collision has to be confirmed in exact arithmetic
(which is what `collision_examples.json`'s exact_signatures and
`verify_witnesses.py` do for the quoted examples).
"""

from __future__ import annotations

import math
from functools import lru_cache

import numpy as np

from graphlib import (
    bipartite,
    degree_sequence,
    diameter,
    degrees,
    distance_matrix,
    edges_of,
    girth,
    is_biconnected,
    is_bridge,
    n_bridges,
    n_components,
    n_edges,
    popcount,
)

SCALE = 10**9


def Q(x: float) -> int:
    """Quantise a float invariant for exact comparison/hashing."""
    return int(round(x * SCALE))


# --------------------------------------------------------------------------
# spectra & polynomials
# --------------------------------------------------------------------------
def _numpy_adj(adj) -> np.ndarray:
    n = len(adj)
    A = np.zeros((n, n), dtype=float)
    for i, m in enumerate(adj):
        while m:
            b = m & -m
            j = b.bit_length() - 1
            m ^= b
            A[i, j] = 1.0
    return A


def _laplacian(adj):
    n = len(adj)
    A = _numpy_adj(adj)
    d = A.sum(axis=1)
    return np.diag(d) - A


def _signless_laplacian(adj):
    A = _numpy_adj(adj)
    d = A.sum(axis=1)
    return np.diag(d) + A


def adj_spectrum(adj):
    ev = np.linalg.eigvalsh(_numpy_adj(adj))
    return tuple(ev)


def lap_spectrum(adj):
    ev = np.linalg.eigvalsh(_laplacian(adj))
    return tuple(ev)


def signless_lap_spectrum(adj):
    ev = np.linalg.eigvalsh(_signless_laplacian(adj))
    return tuple(ev)


def charpoly_coeffs(adj):
    """Coefficients of det(xI - A), exact integers (A is a 0/1 matrix).

    Computed from the numerically obtained eigenvalues then rounded; the
    rounding is validated against sympy in ``validate.py``.  The empty graph
    (a vertex deck can contain it) has characteristic polynomial 1.
    """
    if len(adj) == 0:
        return (1,)
    ev = np.linalg.eigvalsh(_numpy_adj(adj))
    c = np.poly(ev)  # monic, descending
    return tuple(int(round(v)) for v in c)


def lap_charpoly_coeffs(adj):
    if len(adj) == 0:
        return (1,)
    ev = np.linalg.eigvalsh(_laplacian(adj))
    c = np.poly(ev)
    return tuple(int(round(v)) for v in c)


def bareiss_det(M: list[list[int]]) -> int:
    """Exact integer determinant (Bareiss fraction-free elimination)."""
    n = len(M)
    if n == 0:
        return 1
    A = [row[:] for row in M]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            piv = None
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    piv = i
                    break
            if piv is None:
                return 0
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
        for i in range(k + 1, n):
            A[i][k] = 0
    return sign * A[n - 1][n - 1]


def n_spanning_trees(adj) -> int:
    """Matrix-tree theorem; 0 for disconnected graphs."""
    n = len(adj)
    if n <= 1:
        return 1 if n == 1 else 0
    if n_components(adj) != 1:
        return 0
    deg = degrees(adj)
    L = [[0] * (n - 1) for _ in range(n - 1)]
    for i in range(1, n):
        for j in range(1, n):
            if i == j:
                L[i - 1][j - 1] = deg[i]
            elif (adj[i] >> j) & 1:
                L[i - 1][j - 1] = -1
    return bareiss_det(L)


# --------------------------------------------------------------------------
# matching polynomial
# --------------------------------------------------------------------------
def matching_counts(adj) -> tuple[int, ...]:
    """``mk[k]`` = number of k-edge matchings (k = 0..floor(n/2))."""
    n = len(adj)
    adjl = list(adj)
    memo: dict[int, tuple[int, ...]] = {}

    def rec(mask: int) -> tuple[int, ...]:
        if mask == 0:
            return (1,)
        got = memo.get(mask)
        if got is not None:
            return got
        v = (mask & -mask).bit_length() - 1
        rest = mask & ~(1 << v)
        res = list(rec(rest))
        nb = adjl[v] & rest
        while nb:
            b = nb & -nb
            u = b.bit_length() - 1
            nb ^= b
            sub = rec(rest & ~(1 << u))
            for k, val in enumerate(sub, start=1):
                if k >= len(res):
                    res.append(val)
                else:
                    res[k] += val
        out = tuple(res)
        memo[mask] = out
        return out
    # The recursion removes the lowest-index vertex at every step (matched or
    # not), so every k-matching is generated exactly once -- no k! correction.
    return rec((1 << n) - 1)


# --------------------------------------------------------------------------
# chromatic number / max clique (exact, n <= 12)
# --------------------------------------------------------------------------
def clique_number(adj) -> int:
    n = len(adj)
    best = 1 if n else 0

    def expand(R: int, P: int, size: int):
        nonlocal best
        if P == 0:
            best = max(best, size)
            return
        if size + popcount(P) <= best:
            return
        while P:
            if size + popcount(P) <= best:
                return
            b = P & -P
            v = b.bit_length() - 1
            P ^= b
            expand(R | b, P & adj[v], size + 1)

    expand(0, (1 << n) - 1, 0)
    return best


def independence_number(adj) -> int:
    n = len(adj)
    comp = [((1 << n) - 1) & ~adj[i] & ~(1 << i) for i in range(n)]
    return clique_number(tuple(comp))


def chromatic_number(adj) -> int:
    """Exact chromatic number by DSATUR-style branch and bound."""
    n = len(adj)
    if n == 0:
        return 0
    order = sorted(range(n), key=lambda v: -popcount(adj[v]))
    adjl = list(adj)
    best = [n + 1]
    color = [-1] * n

    def feasible(v, c):
        m = adjl[v]
        while m:
            b = m & -m
            u = b.bit_length() - 1
            m ^= b
            if color[u] == c:
                return False
        return True

    def rec(i, used):
        if used >= best[0]:
            return
        if i == n:
            best[0] = used
            return
        v = order[i]
        for c in range(used):
            if feasible(v, c):
                color[v] = c
                rec(i + 1, used)
                color[v] = -1
        color[v] = used
        rec(i + 1, used + 1)
        color[v] = -1

    rec(0, 0)
    return best[0]


# --------------------------------------------------------------------------
# degree based topological indices
# --------------------------------------------------------------------------
def _edge_deg_pairs(adj):
    deg = degrees(adj)
    for u, v in edges_of(adj):
        yield deg[u], deg[v]


def sombor(adj) -> float:
    return sum(math.sqrt(du * du + dv * dv) for du, dv in _edge_deg_pairs(adj))


def sombor_inverse(adj) -> float:
    """1/SO (a.k.a. inverse Sombor): sum 1/sqrt(du^2+dv^2)."""
    return sum(1.0 / math.sqrt(du * du + dv * dv) for du, dv in _edge_deg_pairs(adj))


def sombor_squared(adj) -> float:
    """'Sombor-squared' variant: sum over edges of (du^2+dv^2)."""
    return float(sum(du * du + dv * dv for du, dv in _edge_deg_pairs(adj)))


def sombor_reduced(adj) -> float:
    """Reduced Sombor (Sörensen) style variant: sum sqrt((du-1)^2+(dv-1)^2)."""
    return sum(math.sqrt((du - 1) ** 2 + (dv - 1) ** 2) for du, dv in _edge_deg_pairs(adj))


def randic(adj) -> float:
    return sum(1.0 / math.sqrt(du * dv) for du, dv in _edge_deg_pairs(adj))


def abc(adj) -> float:
    s = 0.0
    for du, dv in _edge_deg_pairs(adj):
        x = (du + dv - 2) / (du * dv)
        if x > 0:
            s += math.sqrt(x)
    return s


def zagreb_m1(adj) -> float:
    return float(sum(d * d for d in degrees(adj)))


def zagreb_m2(adj) -> float:
    return float(sum(du * dv for du, dv in _edge_deg_pairs(adj)))


def forgotten(adj) -> float:
    return float(sum(d**3 for d in degrees(adj)))


def harmonic(adj) -> float:
    return sum(2.0 / (du + dv) for du, dv in _edge_deg_pairs(adj))


def geometric_arithmetic(adj) -> float:
    return sum(2.0 * math.sqrt(du * dv) / (du + dv) for du, dv in _edge_deg_pairs(adj))


def sum_connectivity(adj) -> float:
    return sum(1.0 / math.sqrt(du + dv) for du, dv in _edge_deg_pairs(adj))


def inverse_sum_indeg(adj) -> float:
    return sum(du * dv / (du + dv) for du, dv in _edge_deg_pairs(adj))


def augmented_zagreb(adj) -> float:
    s = 0.0
    for du, dv in _edge_deg_pairs(adj):
        x = du + dv - 2
        if x > 0:
            s += (du * dv / x) ** 3
    return s


# --------------------------------------------------------------------------
# distance based
# --------------------------------------------------------------------------
def distance_profile(adj):
    """(distance distribution, wiener index, diameter, eccentricity sequence)."""
    dm = distance_matrix(adj)
    n = len(adj)
    maxd = 0
    for row in dm:
        for d in row:
            if d > maxd:
                maxd = d
    counts = [0] * (maxd + 1)
    wiener = 0
    for i in range(n):
        for j in range(i + 1, n):
            d = dm[i][j]
            if d > 0:
                counts[d] += 1
                wiener += d
    ecc = tuple(sorted((max(row) if max(row) >= 0 else 0 for row in dm), reverse=True))
    return tuple(counts[1:]), wiener, maxd, ecc


def component_sizes(adj) -> tuple[int, ...]:
    """Sizes of the connected components, in decreasing order.

    The BFS counts each frontier *including* the seed vertex, so an isolated
    vertex is reported as 1 (an earlier version omitted the seed and reported
    every component one short, i.e. 0 for an isolated vertex).
    """
    n = len(adj)
    seen = 0
    sizes = []
    for s in range(n):
        if seen >> s & 1:
            continue
        frontier = 1 << s
        seen |= frontier
        cnt = 1
        while frontier:
            nxt = 0
            f = frontier
            while f:
                b = f & -f
                i = b.bit_length() - 1
                f ^= b
                nxt |= adj[i]
            nxt &= ~seen
            seen |= nxt
            frontier = nxt
            cnt += popcount(frontier)
        sizes.append(cnt)
    return tuple(sorted(sizes, reverse=True))


def n_cut_vertices(adj) -> int:
    """Number of cut vertices (articulation points) of the graph.

    ``G - v`` is formed by isolating ``v`` (which keeps the vertex set, so ``v``
    itself becomes one extra component); the number of components of ``G - v``
    is therefore ``n_components(isolated v) - 1``.
    """
    n = len(adj)
    base = n_components(adj)
    cnt = 0
    for v in range(n):
        a = list(adj)
        for i in range(n):
            if i != v:
                a[i] &= ~(1 << v)
        a[v] = 0
        if n_components(tuple(a)) - 1 > base:
            cnt += 1
    return cnt


# --------------------------------------------------------------------------
# the invariant vector of one graph
# --------------------------------------------------------------------------
# name -> (kind, extractor)
#   kind 'num'  : real number, quantised before hashing
#   kind 'tup'  : tuple of real numbers, each quantised
#   kind 'int'  : integer
#   kind 'ituple': tuple of integers
INVARIANTS: list[str] = [
    # --- size / degree structure
    "n", "m", "deg_seq", "edge_types", "comp_sizes", "n_comp",
    "max_deg", "min_deg", "n_leaves",
    # --- cycles / connectivity structure
    "tri", "clique", "indep", "chrom", "girth", "n_bridges", "n_cut",
    "bipartite", "forest", "biconnected", "diam", "ecc_seq", "dist_dist",
    "max_match", "match_poly", "n_perfect_match", "taus",
    # --- degree based indices
    "sombor", "sombor_inv", "sombor_sq", "sombor_red", "randic", "abc",
    "m1", "m2", "forgotten", "harmonic", "ga", "sum_conn", "isi", "az",
    # --- spectral
    "adj_spec", "lap_spec", "q_spec", "adj_charpoly", "lap_charpoly",
    "energy", "spectral_radius",
    # --- distance based
    "wiener",
]

# invariants whose card values are numbers (used for float quantisation)
_FLOAT_NAMES = {
    "sombor", "sombor_inv", "sombor_sq", "sombor_red", "randic", "abc",
    "m1", "m2", "forgotten", "harmonic", "ga", "sum_conn", "isi", "az",
    "energy", "spectral_radius", "wiener",
}
_TUPLE_FLOAT_NAMES = {"adj_spec", "lap_spec", "q_spec", "ecc_seq"}


def fingerprint(adj) -> dict:
    """All invariants of a single graph, as a plain dict of python objects."""
    n = len(adj)
    deg = degrees(adj)
    dseq = tuple(sorted(deg, reverse=True))
    et = tuple(sorted((min(a, b), max(a, b)) for a, b in _edge_deg_pairs(adj)))
    dist_dist, wiener, diam, ecc = distance_profile(adj)
    mp = matching_counts(adj)
    max_match = max((k for k, c in enumerate(mp) if c > 0), default=0)
    n_perfect = mp[n // 2] if n % 2 == 0 and len(mp) > n // 2 else 0
    a_spec = adj_spectrum(adj)
    l_spec = lap_spectrum(adj)
    q_spec = signless_lap_spectrum(adj)
    return {
        "n": n,
        "m": n_edges(adj),
        "deg_seq": dseq,
        "edge_types": et,
        "comp_sizes": component_sizes(adj),
        "n_comp": n_components(adj),
        "max_deg": max(deg) if deg else 0,
        "min_deg": min(deg) if deg else 0,
        "n_leaves": sum(1 for d in deg if d == 1),
        "tri": sum(popcount(adj[u] & adj[v]) for u, v in edges_of(adj)) // 3,
        "clique": clique_number(adj),
        "indep": independence_number(adj),
        "chrom": chromatic_number(adj),
        "girth": girth(adj),
        "n_bridges": n_bridges(adj),
        "n_cut": n_cut_vertices(adj),
        "bipartite": int(bipartite(adj)),
        "forest": int(n_edges(adj) == n - n_components(adj)),
        "biconnected": int(is_biconnected(adj)),
        "diam": diam,
        "ecc_seq": ecc,
        "dist_dist": dist_dist,
        "max_match": max_match,
        "match_poly": mp,
        "n_perfect_match": n_perfect,
        "taus": n_spanning_trees(adj),
        "sombor": sombor(adj),
        "sombor_inv": sombor_inverse(adj),
        "sombor_sq": sombor_squared(adj),
        "sombor_red": sombor_reduced(adj),
        "randic": randic(adj),
        "abc": abc(adj),
        "m1": zagreb_m1(adj),
        "m2": zagreb_m2(adj),
        "forgotten": forgotten(adj),
        "harmonic": harmonic(adj),
        "ga": geometric_arithmetic(adj),
        "sum_conn": sum_connectivity(adj),
        "isi": inverse_sum_indeg(adj),
        "az": augmented_zagreb(adj),
        "adj_spec": tuple(a_spec),
        "lap_spec": tuple(l_spec),
        "q_spec": tuple(q_spec),
        "adj_charpoly": charpoly_coeffs(adj),
        "lap_charpoly": lap_charpoly_coeffs(adj),
        "energy": float(np.sum(np.abs(a_spec))),
        "spectral_radius": float(max(a_spec)) if len(a_spec) else 0.0,
        "wiener": wiener,
    }


def quantise(name: str, value):
    """Canonical, hashable, quantised representation of one invariant value."""
    if name in _FLOAT_NAMES:
        return Q(float(value))
    if name in _TUPLE_FLOAT_NAMES:
        return tuple(Q(float(x)) for x in value)
    if isinstance(value, tuple):
        return value
    return value


def quantised_fingerprint(adj) -> dict:
    fp = fingerprint(adj)
    return {k: quantise(k, v) for k, v in fp.items()}
