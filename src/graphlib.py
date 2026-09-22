"""
graphlib.py -- core graph representation, canonical labelling and enumeration.

Representation
--------------
A graph on ``n`` vertices is stored as a tuple ``adj`` of ``n`` ints, where bit
``j`` of ``adj[i]`` is 1 iff ``ij`` is an edge (``i != j``).  Self loops are not
representable.  This is compact and fast for the small orders (n <= 9) that this
study uses.

Canonical form
--------------
``canon_cert(adj)`` returns the *nauty certificate* of the graph (a bytes
object).  Two graphs are isomorphic iff their certificates are equal.  The
certificate is produced by ``pynauty`` (nauty 2.8.x, dense representation), and
is used throughout as the unique key of an isomorphism class.  This is the
critical primitive: every comparison in this study is made on certificates, so
no comparison can be polluted by a labelling artefact.
"""

from __future__ import annotations

import itertools
from typing import Iterable, Sequence

import pynauty

# --------------------------------------------------------------------------
# popcount table for masks up to 2**16 (n <= 9 needs 2**9)
# --------------------------------------------------------------------------
_POP = bytes(bin(i).count("1") for i in range(1 << 16))


def popcount(x: int) -> int:
    c = 0
    while x:
        c += _POP[x & 0xFFFF]
        x >>= 16
    return c


# --------------------------------------------------------------------------
# basic constructors
# --------------------------------------------------------------------------
def empty_graph(n: int) -> tuple[int, ...]:
    return tuple([0] * n)


def from_edges(n: int, edges: Iterable[tuple[int, int]]) -> tuple[int, ...]:
    adj = [0] * n
    for u, v in edges:
        if u == v:
            raise ValueError("no self loops")
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return tuple(adj)


def edges_of(adj: Sequence[int]) -> list[tuple[int, int]]:
    out = []
    for u in range(len(adj)):
        m = adj[u] >> (u + 1)
        while m:
            b = m & -m
            v = b.bit_length() - 1 + u + 1
            out.append((u, v))
            m ^= b
    return out


def n_vertices(adj: Sequence[int]) -> int:
    return len(adj)


def n_edges(adj: Sequence[int]) -> int:
    return sum(popcount(m) for m in adj) // 2


def degrees(adj: Sequence[int]) -> tuple[int, ...]:
    return tuple(popcount(m) for m in adj)


def degree_sequence(adj: Sequence[int]) -> tuple[int, ...]:
    return tuple(sorted(degrees(adj), reverse=True))


def max_degree(adj: Sequence[int]) -> int:
    return max((popcount(m) for m in adj), default=0)


def relabel(adj: Sequence[int], perm: Sequence[int]) -> tuple[int, ...]:
    """Return the graph whose vertex ``i`` is old vertex ``perm[i]``."""
    n = len(adj)
    out = [0] * n
    for i in range(n):
        pi = perm[i]
        m = adj[pi]
        while m:
            b = m & -m
            j = b.bit_length() - 1
            m ^= b
            out[i] |= 1 << perm.index(j)
    return tuple(out)


def permute(adj: Sequence[int], perm: Sequence[int]) -> tuple[int, ...]:
    """Faster relabel: new adjacency of vertex i is {perm[j] : j in N(i)}."""
    n = len(adj)
    out = [0] * n
    for i in range(n):
        m = adj[i]
        acc = 0
        while m:
            b = m & -m
            j = b.bit_length() - 1
            m ^= b
            acc |= 1 << perm[j]
        out[perm[i]] = acc
    return tuple(out)


# --------------------------------------------------------------------------
# canonical labelling / certificate
# --------------------------------------------------------------------------
_CERT_CACHE: dict[tuple[int, ...], bytes] = {}


def _to_pynauty(adj: Sequence[int]) -> pynauty.Graph:
    d = {}
    for i, m in enumerate(adj):
        lst = []
        mm = m
        while mm:
            b = mm & -mm
            lst.append(b.bit_length() - 1)
            mm ^= b
        d[i] = lst
    return pynauty.Graph(len(adj), adjacency_dict=d, directed=False)


def canon_cert(adj: Sequence[int], cache: bool = True) -> bytes:
    """Canonical certificate (isomorphism-class key) of a graph."""
    key = tuple(adj)
    if cache:
        c = _CERT_CACHE.get(key)
        if c is not None:
            return c
    c = pynauty.certificate(_to_pynauty(adj))
    if cache:
        _CERT_CACHE[key] = c
    return c


def canon_cert_hex(adj: Sequence[int]) -> str:
    return canon_cert(adj).hex()


def canonical_order(adj: Sequence[int]) -> list[int]:
    """A canonical vertex order (labelling) of the graph."""
    return pynauty.canon_label(_to_pynauty(adj))


def isomorphic(adj1: Sequence[int], adj2: Sequence[int]) -> bool:
    if len(adj1) != len(adj2):
        return False
    if n_edges(adj1) != n_edges(adj2):
        return False
    return canon_cert(adj1) == canon_cert(adj2)


# --------------------------------------------------------------------------
# graph6 (for exchange and for the report appendix)
# --------------------------------------------------------------------------
def to_graph6(adj: Sequence[int]) -> str:
    n = len(adj)
    if n == 0:
        return ""
    bits: list[int] = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (adj[i] >> j) & 1 else 0)
    # pad to multiple of 6
    pad = (-len(bits)) % 6
    bits.extend([0] * pad)
    chars = []
    for k in range(0, len(bits), 6):
        val = 0
        for b in bits[k : k + 6]:
            val = (val << 1) | b
        chars.append(chr(val + 63))
    if n <= 62:
        head = chr(n + 63)
    else:  # pragma: no cover - not used for n <= 9
        head = "~" + "".join(chr(63 + ((n >> s) & 0x3F)) for s in (12, 6, 0))
    return head + "".join(chars)


def from_graph6(s: str) -> tuple[int, ...]:
    s = s.strip()
    if s.startswith(">>graph6<<"):
        s = s[10:]
    if not s:
        return ()
    if s[0] == "~":  # pragma: no cover
        raise NotImplementedError("n > 62 not needed")
    n = ord(s[0]) - 63
    bits: list[int] = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for sft in (5, 4, 3, 2, 1, 0):
            bits.append((v >> sft) & 1)
    adj = [0] * n
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return tuple(adj)


# --------------------------------------------------------------------------
# enumeration of all graphs / connected graphs of order n
# --------------------------------------------------------------------------
def enumerate_graphs_by_order(
    n_max: int,
    maxdeg: int | None = None,
    require_connected: bool = False,
) -> list[dict[int, tuple[int, ...]]]:
    """Enumerate all non-isomorphic simple graphs of each order <= n_max.

    Orderly generation by vertex extension: every graph on k+1 vertices arises
    from some graph on k vertices by attaching the new vertex to an arbitrary
    subset of the old vertices, so the extension is complete.  Duplicates are
    removed with the nauty certificate.

    ``maxdeg`` restricts the *maximum degree of the final graph* (used for
    chemical graphs, maxdeg=4).  ``require_connected`` keeps only connected
    graphs in the returned levels.  It is applied as a *post-filter*: the
    generation itself must keep disconnected graphs at intermediate orders,
    because deleting a cut vertex of a connected graph disconnects it, so
    connected graphs of order k+1 can arise from disconnected graphs of
    order k.
    Returns ``levels[k] = {cert: adj}``.
    """
    levels: list[dict[int, tuple[int, ...]]] = [dict()]
    cur: dict[bytes, tuple[int, ...]] = {canon_cert(empty_graph(1)): empty_graph(1)}
    levels.append(cur)
    for k in range(1, n_max):
        nxt: dict[bytes, tuple[int, ...]] = {}
        degs_ok_prev = None
        for cert, adj in cur.items():
            degs = degrees(adj)
            if maxdeg is not None:
                degs_ok_prev = [d < maxdeg for d in degs]
            # choose neighbours of the new vertex k
            allowed = [i for i in range(k) if maxdeg is None or degs[i] < maxdeg]
            for r in range(0, len(allowed) + 1):
                if maxdeg is not None and r > maxdeg:
                    break
                for comb in itertools.combinations(allowed, r):
                    newadj = list(adj) + [0]
                    m = 0
                    for i in comb:
                        m |= 1 << i
                        newadj[i] |= 1 << k
                    newadj[k] = m
                    t = tuple(newadj)
                    c = canon_cert(t)
                    if c not in nxt:
                        nxt[c] = t
        cur = nxt
        levels.append(cur)
    if require_connected:
        # Post-filter (see docstring): pruning during generation would lose
        # connected graphs whose vertex deletions are disconnected.
        levels = [
            {} if k == 0 else {c: a for c, a in lv.items() if connected(a)}
            for k, lv in enumerate(levels)
        ]
    return levels


# --------------------------------------------------------------------------
# structural predicates / descriptors used for metadata (pure python, fast)
# --------------------------------------------------------------------------
def connected(adj: Sequence[int]) -> bool:
    n = len(adj)
    if n == 0:
        return False
    seen = 1
    frontier = 1
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
    return seen == (1 << n) - 1


def n_components(adj: Sequence[int]) -> int:
    n = len(adj)
    seen = 0
    comps = 0
    for s in range(n):
        if seen >> s & 1:
            continue
        comps += 1
        frontier = 1 << s
        seen |= frontier
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
    return comps


def is_forest(adj: Sequence[int]) -> bool:
    return n_edges(adj) == len(adj) - n_components(adj)


def bipartite(adj: Sequence[int]) -> bool:
    n = len(adj)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            m = adj[u]
            while m:
                b = m & -m
                v = b.bit_length() - 1
                m ^= b
                if color[v] == -1:
                    color[v] = color[u] ^ 1
                    stack.append(v)
                elif color[v] == color[u]:
                    return False
    return True


def bfs_dist(adj: Sequence[int], s: int) -> list[int]:
    """Distances from ``s``; -1 for unreachable vertices."""
    n = len(adj)
    dist = [-1] * n
    dist[s] = 0
    seen = 1 << s
    frontier = 1 << s
    d = 0
    while frontier:
        d += 1
        nxt = 0
        f = frontier
        while f:
            b = f & -f
            i = b.bit_length() - 1
            f ^= b
            nxt |= adj[i]
        nxt &= ~seen
        seen |= nxt
        f2 = nxt
        while f2:
            b = f2 & -f2
            i = b.bit_length() - 1
            f2 ^= b
            dist[i] = d
        frontier = nxt
    return dist


def distance_matrix(adj: Sequence[int]) -> list[list[int]]:
    n = len(adj)
    dm = [[-1] * n for _ in range(n)]
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        seen = 1 << s
        frontier = 1 << s
        d = 0
        while frontier:
            d += 1
            nxt = 0
            f = frontier
            while f:
                b = f & -f
                i = b.bit_length() - 1
                f ^= b
                nxt |= adj[i]
            nxt &= ~seen
            f2 = nxt
            while f2:
                b = f2 & -f2
                i = b.bit_length() - 1
                f2 ^= b
                dist[i] = d
            seen |= nxt
            frontier = nxt
        dm[s] = dist
    return dm


def distance_distribution(adj: Sequence[int]) -> tuple[int, ...]:
    """Number of unordered vertex pairs at distance 1,2,3,... (connected graph)."""
    dm = distance_matrix(adj)
    n = len(adj)
    maxd = max((d for row in dm for d in row), default=0)
    if maxd < 0:
        return ()
    counts = [0] * (maxd + 1)
    for i in range(n):
        for j in range(i + 1, n):
            d = dm[i][j]
            if d > 0:
                counts[d] += 1
    return tuple(counts[1:])


def eccentricities(adj: Sequence[int]) -> tuple[int, ...]:
    dm = distance_matrix(adj)
    return tuple(max(r) for r in dm)


def diameter(adj: Sequence[int]) -> int:
    if not connected(adj):
        return -1
    return max(eccentricities(adj))


def _reach(adj: Sequence[int], s: int) -> int:
    """Bitmask of the connected component containing s."""
    seen = 1 << s
    frontier = 1 << s
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
    return seen


def _dist_without_edge(adj: Sequence[int], u: int, v: int) -> list[int]:
    """BFS distances from u in G - uv."""
    n = len(adj)
    a = list(adj)
    a[u] &= ~(1 << v)
    a[v] &= ~(1 << u)
    dist = [-1] * n
    dist[u] = 0
    seen = 1 << u
    frontier = 1 << u
    d = 0
    while frontier:
        d += 1
        nxt = 0
        f = frontier
        while f:
            b = f & -f
            i = b.bit_length() - 1
            f ^= b
            nxt |= a[i]
        nxt &= ~seen
        seen |= nxt
        f2 = nxt
        while f2:
            b = f2 & -f2
            i = b.bit_length() - 1
            f2 ^= b
            dist[i] = d
        frontier = nxt
    return dist


def girth(adj: Sequence[int]) -> int:
    """Length of the shortest cycle, or 0 when the graph is acyclic."""
    best = 1 << 30
    for u, v in edges_of(adj):
        d = _dist_without_edge(adj, u, v)[v]
        if d > 0:
            best = min(best, d + 1)
    return 0 if best == 1 << 30 else best


def is_bridge(adj: Sequence[int], u: int, v: int) -> bool:
    """True iff uv is a bridge: removing it grows the component count."""
    before = popcount(_reach(adj, u))
    a = list(adj)
    a[u] &= ~(1 << v)
    a[v] &= ~(1 << u)
    after = popcount(_reach(tuple(a), u))
    return after < before


def n_bridges(adj: Sequence[int]) -> int:
    return sum(1 for u, v in edges_of(adj) if is_bridge(adj, u, v))


def is_biconnected(adj: Sequence[int]) -> bool:
    """2-connected: connected, >=3 vertices, no cut vertex."""
    n = len(adj)
    if n < 3 or not connected(adj):
        return False
    for v in range(n):
        a = list(adj)
        rest = [i for i in range(n) if i != v]
        for i in rest:
            a[i] &= ~(1 << v)
        a[v] = 0
        sub = tuple(a)
        # connectivity among rest
        if not rest:
            continue
        s = rest[0]
        seen = 1 << s
        frontier = 1 << s
        while frontier:
            nxt = 0
            f = frontier
            while f:
                b = f & -f
                i = b.bit_length() - 1
                f ^= b
                nxt |= sub[i]
            nxt &= ~seen
            seen |= nxt
            frontier = nxt
        if popcount(seen & sum(1 << i for i in rest)) != len(rest):
            return False
    return True
