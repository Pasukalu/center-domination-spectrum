"""Exhaust graphs through seven vertices up to relabelling, using only Python."""
from itertools import combinations, permutations, product


def distances(adj):
    n = len(adj)
    d = [[0 if i == j else 1 if j in adj[i] else n for j in range(n)]
         for i in range(n)]
    for k in range(n):
        for i in range(n):
            for j in range(n):
                d[i][j] = min(d[i][j], d[i][k] + d[k][j])
    return d


def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for i, j in edges:
        adj[i].add(j)
        adj[j].add(i)
    return adj


def components(adj, vertices):
    unseen = set(vertices)
    count = 0
    while unseen:
        stack = [unseen.pop()]
        count += 1
        while stack:
            fresh = unseen & adj[stack.pop()]
            unseen -= fresh
            stack.extend(fresh)
    return count


def tree_list(n, bits):
    result = []
    for word in product(range(n), repeat=n - 2):
        degree = [1 + word.count(i) for i in range(n)]
        edges = []
        for parent in word:
            leaf = degree.index(1)
            edges.append((leaf, parent))
            degree[leaf] -= 1
            degree[parent] -= 1
        edges.append(tuple(i for i in range(n) if degree[i] == 1))
        d = distances(adjacency(n, edges))
        mask = sum(bits[tuple(sorted(edge))] for edge in edges)
        result.append((max(map(max, d)), mask))
    return sorted(result)


def check_connected(n, adj, d, mask, trees):
    vertices = set(range(n))
    best_tree = next(diam for diam, tree in trees if tree & mask == tree)
    total_sets = [set(D) for k in range(2, n + 1) for D in combinations(range(n), k)
                  if all(neighbors.intersection(D) for neighbors in adj)]
    k = min(map(len, total_sets))
    for D in total_sets:
        c = components(adj, D)
        assert 2 * c <= len(D) and best_tree <= len(D) + 2 * c - 1
    eccentricity = [max(row) for row in d]
    radius = min(eccentricity)
    center = {i for i in vertices if eccentricity[i] == radius}
    pairs = list(combinations(sorted(center), 2))
    numerator = sum(d[i][j] for i, j in pairs)
    denominator = max(1, len(pairs))
    assert numerator < k * denominator
    if k % 2:
        assert numerator <= (k - 1) * denominator
    c4_free = all(len(adj[i] & adj[j]) <= 1 for i, j in combinations(vertices, 2))
    if c4_free:
        assert numerator <= (k - 1) * denominator
    if center != vertices:
        assert len(vertices - center) >= 2
    if k == 2 and pairs:
        edges = sum(j in adj[i] for i, j in pairs)
        assert components(adj, center) == 1
        assert len(center) - 1 <= edges <= len(pairs)
        assert numerator == 2 * denominator - edges
        assert any(center <= (adj[i] | adj[j]) for i, j in pairs if j in adj[i])


def exhaust(n):
    edges = list(combinations(range(n), 2))
    bits = {edge: 1 << i for i, edge in enumerate(edges)}
    maps = [tuple(bits[tuple(sorted((p[i], p[j])))] for i, j in edges)
            for p in permutations(range(n))]
    seen = bytearray(1 << len(edges))
    trees = tree_list(n, bits)
    classes = labelled = total = 0
    for mask in range(len(seen)):
        if seen[mask]:
            continue
        indices = [i for i in range(len(edges)) if mask & (1 << i)]
        orbit = {sum(mapping[i] for i in indices) for mapping in maps}
        for other in orbit:
            seen[other] = 1
        total += len(orbit)
        adj = adjacency(n, (edges[i] for i in indices))
        d = distances(adj)
        if max(d[0]) == n:
            continue
        check_connected(n, adj, d, mask, trees)
        classes += 1
        labelled += len(orbit)
    assert total == len(seen)
    return classes, labelled


def pendant_examples():
    edges = list(product(range(2), range(2, 6)))
    for vertex, expected in [(0, (5, 16, 10)), (2, (3, 4, 3))]:
        d = distances(adjacency(7, edges + [(vertex, 6)]))
        radius = min(map(max, d))
        center = [i for i, row in enumerate(d) if max(row) == radius]
        pairs = list(combinations(center, 2))
        observed = len(center), sum(d[i][j] for i, j in pairs), len(pairs)
        assert observed == expected
        print(f"Pendant at {vertex}: {observed[0]} centers, mean {observed[1]}/{observed[2]}")


if __name__ == "__main__":
    print("order  connected isomorphism classes  connected labelled graphs", flush=True)
    for n in range(2, 8):
        classes, labelled = exhaust(n)
        print(f"{n:5}  {classes:29}  {labelled:25}", flush=True)
    pendant_examples()
