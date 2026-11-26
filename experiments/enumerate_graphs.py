"""Exact pilots for five WOWII conjectures and the center-distance spectrum.

Python 3.10+. All reported means use Fraction. Labelled graphs are not
deduplicated up to isomorphism. This is an experimental check of the proofs.
"""
from __future__ import annotations
import argparse
import itertools
import json
import random
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def graph(n, edges):
    adj = [0] * n
    for a, b in edges:
        assert 0 <= a < n and 0 <= b < n and a != b
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return adj


def neighborhood(adj, mask):
    result = 0
    for i in bits(mask):
        result |= adj[i]
    return result


def reaches(adj, domain):
    seen = frontier = domain & -domain
    while frontier:
        frontier = neighborhood(adj, frontier) & domain & ~seen
        seen |= frontier
    return seen == domain


def all_distances(adj):
    n = len(adj)
    rows = []
    for i in range(n):
        dist = [-1] * n
        dist[i] = 0
        queue = [i]
        for x in queue:
            for y in bits(adj[x]):
                if dist[y] == -1:
                    dist[y] = dist[x] + 1
                    queue.append(y)
        rows.append(dist)
    return rows


def invariants(adj):
    n = len(adj)
    whole = (1 << n) - 1
    distances = all_distances(adj)
    assert all(min(row) >= 0 for row in distances)
    ecc = list(map(max, distances))
    radius = min(ecc)
    center = [i for i in range(n) if ecc[i] == radius]
    pairs = list(itertools.combinations(center, 2))
    mean = Fraction(sum(distances[i][j] for i, j in pairs), len(pairs) or 1)
    # For n >= 3 a spanning tree's internal vertices are a connected
    # dominating set, and a minimum such set extends to a spanning tree.
    td, cd = n, n
    for size in range(1, n + 1):
        for subset in itertools.combinations(range(n), size):
            mask = sum(1 << i for i in subset)
            neighbors = neighborhood(adj, mask)
            if neighbors == whole:
                td = min(td, size)
            if (neighbors | mask) == whole and reaches(adj, mask):
                cd = min(cd, size)
        if td <= size and cd <= size:
            break
    leaves = n - cd if n > 2 else 2
    degree = [x.bit_count() for x in adj]
    selectors = [
        [i for i in range(n) if degree[i] == max(degree)],
        [i for i in range(n) if ecc[i] == max(ecc)],
        [i for i in range(n) if degree[i] == 2],
    ]
    boundaries = []
    for sel in selectors:
        s = sum(1 << i for i in sel)
        boundaries.append((neighborhood(adj, s) & ~s).bit_count())
    c4free = all((adj[i] & adj[j]).bit_count() < 2
                 for i, j in itertools.combinations(range(n), 2))
    return td, radius, center, mean, leaves, boundaries, c4free


def inspect(adj, counters, spectrum):
    k, r, center, a, leaves, boundary, c4free = invariants(adj)
    m = len(center)
    counters['connected'] += 1
    claims = {str(i): k * leaves >= 2 * b for i, b in zip((259, 260, 261), boundary)}
    claims['268'] = a < k
    if c4free:
        claims['269'] = 1 + a <= k
    for label, ok in claims.items():
        counters['tested_' + label] += 1
        counters['violations_' + label] += int(not ok)
        if not ok:
            raise AssertionError((label, adj, k, r, m, str(a), leaves, boundary))
    if k % 2:
        assert r < k
    if r == k:
        # Test the midpoint-edge conclusion independently of its construction.
        d = all_distances(adj)
        assert any((adj[u] >> v) & 1 and
                   all(min(d[u][z], d[v][z]) < k for z in range(len(adj)))
                   for u, v in itertools.combinations(center, 2))
    if k == 2 and m >= 2:
        edges = sum((adj[u] >> v) & 1 for u, v in itertools.combinations(center, 2))
        assert edges >= m - 1 and a == 2 - Fraction(edges, m * (m - 1) // 2)
        spectrum[m].add(a)


def sharp_graph(m, extra):
    # Add 'extra' edges in the large part of K_{2,m-1}, then hang a leaf
    # from the first vertex in the part of size two. Center = {0, 2,...,m}.
    assert m >= 2 and 0 <= extra <= (m - 1) * (m - 2) // 2
    spokes = range(2, m + 1)
    edges = [(0, m + 1)] + [(i, v) for i in (0, 1) for v in spokes]
    edges += list(itertools.islice(itertools.combinations(spokes, 2), extra))
    return graph(m + 2, edges)


def extend_center(h, u, v):
    m = len(h)
    assert ((h[u] >> v) & 1) and (h[u] | h[v]) == (1 << m) - 1
    p, q, a, b = range(m, m + 4)
    edges = [(i, j) for i in range(m) for j in bits(h[i]) if i < j]
    edges += [(p, x) for x in range(m) if x != v]
    edges += [(q, x) for x in range(m) if x != u]
    edges += [(a, v), (a, q), (b, u), (b, p)]
    return graph(m + 4, edges)


def constructive_checks(max_m):
    spectra, extensions = 0, 0
    for m in range(2, max_m + 1):
        pairs = m * (m - 1) // 2
        for extra in range((m - 1) * (m - 2) // 2 + 1):
            g = sharp_graph(m, extra)
            d = all_distances(g)
            ecc = list(map(max, d))
            c = [i for i, e in enumerate(ecc) if e == min(ecc)]
            assert c == [0, *range(2, m + 1)]
            assert (g[0] | g[2]) == (1 << len(g)) - 1
            assert sum(d[u][v] for u, v in itertools.combinations(c, 2)) == 2 * pairs - m + 1 - extra
            spectra += 1
    for n in range(2, 6):
        other = [e for e in itertools.combinations(range(n), 2) if e != (0, 1)]
        for code in range(1 << len(other)):
            h = graph(n, [(0, 1)] + [e for j, e in enumerate(other) if code >> j & 1])
            if h[0] | h[1] != (1 << n) - 1:
                continue
            g = extend_center(h, 0, 1)
            ecc = list(map(max, all_distances(g)))
            assert ecc == [2] * n + [3] * 4
            assert g[0] | g[1] == (1 << len(g)) - 1
            extensions += 1
    return {'spectrum_instances': spectra, 'rooted_center_extensions': extensions}


def run(max_n, sample_count, max_m):
    rows = {}
    spectrum = defaultdict(set)
    for n in range(2, max_n + 1):
        counters = Counter()
        edges = list(itertools.combinations(range(n), 2))
        for code in range(1 << len(edges)):
            adj = graph(n, (edges[j] for j in bits(code)))
            if reaches(adj, (1 << n) - 1):
                inspect(adj, counters, spectrum)
        rows[str(n)] = dict(sorted(counters.items()))
    rng = random.Random(268)
    sampled = Counter()
    for i in range(sample_count):
        n = 7 + i % 8
        # A random recursive spanning tree guarantees connectedness.
        tree = [(v, rng.randrange(v)) for v in range(1, n)]
        additional = [e for e in itertools.combinations(range(n), 2)
                      if rng.randrange(10) < i % 6]
        inspect(graph(n, tree + additional), sampled, spectrum)
    return {'all_labelled': rows, 'sample_seed': 268, 'sample': dict(sorted(sampled.items())),
            'observed_spectrum': {str(m): [str(a) for a in sorted(vals)]
                                  for m, vals in sorted(spectrum.items())},
            'constructive': constructive_checks(max_m),
            'max_family_center_order': max_m}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=6, choices=range(2, 9))
    parser.add_argument('--samples', type=int, default=240)
    parser.add_argument('--family-max', type=int, default=18)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    result = json.dumps(run(args.max_n, args.samples, args.family_max), indent=2) + '\n'
    if args.out:
        args.out.write_text(result, encoding='utf-8')
    else:
        print(result, end='')

