"""Exact, dependency-free checks of Graffiti.pc Conjecture 271 on labeled graphs."""
from collections import deque
from itertools import combinations


def distances(neighbors, start):
    result = [-1] * len(neighbors)
    result[start] = 0
    queue = deque([start])
    while queue:
        vertex = queue.popleft()
        for other in neighbors[vertex]:
            if result[other] == -1:
                result[other] = result[vertex] + 1
                queue.append(other)
    return result


def check_order(n):
    edges = list(combinations(range(n), 2))
    vertices = set(range(n))
    connected = equalities = 0
    for mask in range(1 << len(edges)):
        neighbors = [set() for _ in range(n)]
        for bit, (u, v) in enumerate(edges):
            if mask & (1 << bit):
                neighbors[u].add(v)
                neighbors[v].add(u)
        if -1 in distances(neighbors, 0):
            continue
        connected += 1

        degree = max(map(len, neighbors))
        maxima = [v for v in vertices if len(neighbors[v]) == degree]
        d_max = 0
        for x in maxima:
            row = distances(neighbors, x)
            d_max = max(d_max, max(row[y] for y in maxima))

        k = next(size for size in range(1, n + 1)
                 if any(set().union(*(neighbors[v] for v in subset)) == vertices
                        for subset in combinations(range(n), size)))

        # Check the structural condition directly, independently of k and d_max.
        dominating_edge = any(neighbors[u] | neighbors[v] == vertices
                              for u, v in edges if v in neighbors[u])
        nonadjacent_maxima = any(y not in neighbors[x]
                                 for x, y in combinations(maxima, 2))
        equality = k * k == 2 * d_max
        if k * k < 2 * d_max or equality != (dominating_edge and nonadjacent_maxima):
            raise AssertionError((n, mask, k, d_max))
        equalities += equality
    return connected, equalities


def main():
    expected = {2: (1, 0), 3: (4, 0), 4: (38, 3), 5: (728, 40), 6: (26704, 2365)}
    total = tight = 0
    print("order  connected  equality")
    for n, reference in expected.items():
        connected, equalities = check_order(n)
        if (connected, equalities) != reference:
            raise AssertionError((n, connected, equalities, reference))
        print(f"{n:5d}  {connected:9d}  {equalities:8d}")
        total += connected
        tight += equalities
    print(f"PASS: {total} connected labeled graphs, {tight} unrounded equalities.")


if __name__ == "__main__":
    main()
