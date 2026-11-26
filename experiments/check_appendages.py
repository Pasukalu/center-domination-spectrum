"""Exhaust small extensions of the four-vertex path with exact graph distances."""
from itertools import combinations
from enumerate_graphs import graph, all_distances, reaches


def center(adj):
    if not reaches(adj, (1 << len(adj)) - 1):
        return set()
    eccentricities = [max(row) for row in all_distances(adj)]
    radius = min(eccentricities)
    return {i for i, ecc in enumerate(eccentricities) if ecc == radius}


def path_extensions(extra):
    order = 4 + extra
    original_edges = [(0, 1), (1, 2), (2, 3)]
    optional = [(i, j) for i, j in combinations(range(order), 2) if j >= 4]
    ordinary = preserved = 0
    for mask in range(1 << len(optional)):
        adj = graph(order, original_edges)
        for index, (i, j) in enumerate(optional):
            if mask & (1 << index):
                adj[i] |= 1 << j
                adj[j] |= 1 << i
        if center(adj) == {0, 1, 2, 3}:
            ordinary += 1
            preserved += (adj[1] | adj[2]) == (1 << order) - 1
    return 1 << len(optional), ordinary, preserved


def double_star(left, right):
    leaves = list(range(2, 2 + left + right))
    old = [0, 1, *leaves]
    n = len(old)
    edges = [(0, 1)]
    edges += [(0, leaf) for leaf in leaves[:left]]
    edges += [(1, leaf) for leaf in leaves[left:]]
    ordinary = graph(n + 2, edges + [(n, leaf) for leaf in leaves]
                     + [(n + 1, 0), (n + 1, 1)])
    assert center(ordinary) == set(old)
    assert (ordinary[0] | ordinary[1]) != (1 << (n + 2)) - 1
    p, q, a, b = range(n, n + 4)
    extended = edges + [(p, z) for z in old if z != 1]
    extended += [(q, z) for z in old if z != 0]
    extended += [(a, 1), (a, q), (b, 0), (b, p)]
    rooted = graph(n + 4, extended)
    assert center(rooted) == set(old)
    assert (rooted[0] | rooted[1]) == (1 << (n + 4)) - 1


if __name__ == "__main__":
    print("added  labelled extensions  correct center  edge preserved")
    for k in range(4):
        count, ordinary, preserved = path_extensions(k)
        print(f"{k:5}  {count:19}  {ordinary:14}  {preserved:14}")
        assert preserved == 0
        if k < 2:
            assert ordinary == 0
        if k == 2:
            assert ordinary > 0
    for left in range(1, 9):
        for right in range(1, 9):
            double_star(left, right)
    print("Checked both constructions for 64 double-star parameter pairs.")

