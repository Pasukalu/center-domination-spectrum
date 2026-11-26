"""Independent matrix and subset check. No imports from the primary search."""
import itertools
from fractions import Fraction


def distances(adj):
    n = len(adj)
    d = [[0 if i == j else 1 if adj[i][j] else n + 1
          for j in range(n)] for i in range(n)]
    for k in range(n):
        for i in range(n):
            for j in range(n):
                d[i][j] = min(d[i][j], d[i][k] + d[k][j])
    return d


def tree_masks(n, edge_index):
    # Each labelled spanning tree occurs once as a Pruefer word.
    for word in itertools.product(range(n), repeat=n - 2):
        counts = [1 + word.count(j) for j in range(n)]
        leaves = counts.count(1)
        mask = 0
        for v in word:
            leaf = counts.index(1)
            mask |= 1 << edge_index[tuple(sorted((leaf, v)))]
            counts[v] -= 1
            counts[leaf] -= 1
        a, b = (i for i in range(n) if counts[i] == 1)
        yield mask | (1 << edge_index[a, b]), leaves


def exhaust():
    totals = []
    for n in range(2, 6):
        vertices = set(range(n))
        pairs = list(itertools.combinations(range(n), 2))
        trees = list(tree_masks(n, {e: i for i, e in enumerate(pairs)}))
        valid = 0
        for mask in range(1 << len(pairs)):
            spanning = [leaves for tree, leaves in trees if mask & tree == tree]
            if not spanning:
                continue
            valid += 1
            g = [[False] * n for _ in range(n)]
            for i, (u, v) in enumerate(pairs):
                g[u][v] = g[v][u] = bool(mask >> i & 1)
            d = distances(g)
            ecc = list(map(max, d))
            center = [i for i in range(n) if ecc[i] == min(ecc)]
            cp = list(itertools.combinations(center, 2))
            mean = Fraction(sum(d[i][j] for i, j in cp), len(cp) or 1)
            k = min(len(s) for t in range(2, n + 1)
                    for s in itertools.combinations(vertices, t)
                    if all(any(g[v][w] for w in s) for v in vertices))
            assert mean < k
            if min(ecc) == k:
                assert any(g[u][v] and all(min(d[u][w], d[v][w]) < k for w in vertices)
                           for u, v in cp)
            has_square = any(g[a][b] and g[b][c] and g[c][e] and g[e][a]
                             for a, b, c, e in itertools.permutations(vertices, 4))
            if not has_square:
                assert mean + 1 <= k
            deg = list(map(sum, g))
            for sel in ({i for i in vertices if deg[i] == max(deg)},
                        {i for i in vertices if ecc[i] == max(ecc)},
                        {i for i in vertices if deg[i] == 2}):
                boundary = {v for v in vertices - sel if any(g[v][x] for x in sel)}
                assert 2 * len(boundary) <= k * max(spanning)
        totals.append(valid)
    assert totals == [1, 4, 38, 728]
    print("Independent connected labelled counts, orders 2 to 5:", totals)
    print("Pruefer spanning-tree count and Floyd-Warshall checks passed.")


if __name__ == '__main__':
    exhaust()

