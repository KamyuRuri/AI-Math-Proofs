#!/usr/bin/env python3
"""
Independent exact verification for Graffiti.pc Conjecture 255:
  gamma_t(G) * M(G) >= 2 * |C(G)|
where:
  - gamma_t(G) is the total domination number,
  - M(G) = max_{uv in E(G)} |N(u) union N(v)|,
  - C(G) is the center (set of vertices of minimum eccentricity).

Verifies:
  1. Subdivided-clique family G_t (t = 2..12): t = 5 gives the 11-vertex minimal
     counterexample (n=11, |E|=20, |C|=11, M=7, gamma_t=3, 21 < 22, 5 min sets),
     and the gap is t - 4 throughout the tested range.
  2. Rook-group-apex family H_k (k = 2, 3, 4): all vertices have eccentricity 2
     (|C| = k^4 + k + 1), gamma_t <= k + 1, and M <= k^3 + 2k^2.
  3. Exhaustive check over all simple connected graphs on 2 <= n <= 6 vertices.
"""

from collections import Counter, deque
from itertools import combinations


def analyze_graph(n: int, edges: list[tuple[int, int]], check_gamma_up_to: int | None = None):
    V = range(n)
    N = [set() for _ in V]
    for u, v in edges:
        assert u != v
        N[u].add(v)
        N[v].add(u)

    def eccentricity(start: int) -> int:
        dist = {start: 0}
        q = deque([start])
        while q:
            u = q.popleft()
            for v in N[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    q.append(v)
        assert len(dist) == n, "Graph is not connected"
        return max(dist.values())

    ecc = [eccentricity(v) for v in V]
    min_ecc = min(ecc)
    center = [v for v in V if ecc[v] == min_ecc]
    edge_sizes = Counter(len(N[u] | N[v]) for u, v in edges)
    M = max(edge_sizes)

    gamma_t = None
    min_count = None
    if check_gamma_up_to is not None:
        N_masks = [0] * n
        for u in V:
            mask = 0
            for v in N[u]:
                mask |= 1 << v
            N_masks[u] = mask
        all_mask = (1 << n) - 1
        for s in range(2, min(n, check_gamma_up_to) + 1):
            cnt = 0
            for comb in combinations(V, s):
                # A total dominating set covers V by its members' open neighborhoods.
                cov = 0
                for d in comb:
                    cov |= N_masks[d]
                if cov == all_mask:
                    cnt += 1
            if cnt > 0:
                gamma_t = s
                min_count = cnt
                break
    return {
        "n": n,
        "m": len(edges),
        "ecc": ecc,
        "center": center,
        "edge_sizes": edge_sizes,
        "M": M,
        "gamma_t": gamma_t,
        "min_count": min_count,
        "N": N,
    }


def verify_subdivided_clique():
    print("=== 1. Subdivided-Clique Family G_t (t = 2..12) ===")
    for t in range(2, 13):
        n = 2 * t + 1
        # 0 = apex x; 1..t = clique a_i; t+1..2t = subdivision b_i
        edges = list(combinations(range(1, t + 1), 2))
        edges += [(i, i + t) for i in range(1, t + 1)]
        edges += [(0, i + t) for i in range(1, t + 1)]

        check_lim = n if t <= 7 else 2  # for t > 7 check no 2-edge dom & verify explicit 3-set
        res = analyze_graph(n, edges, check_gamma_up_to=check_lim)
        assert set(res["ecc"]) == {2}
        assert len(res["center"]) == 2 * t + 1
        assert res["edge_sizes"] == {t + 2: len(edges)}
        assert len(edges) == t * (t - 1) // 2 + 2 * t

        # Explicit 3-vertex total dominating set {0, 1, t+1}
        D3 = {0, 1, t + 1}
        assert all(res["N"][v] & D3 for v in range(n))
        if t <= 7:
            assert res["gamma_t"] == 3
            gamma = res["gamma_t"]
        else:
            # Since M = t + 2 < 2t + 1 = n, no edge's neighborhood union covers V, so gamma_t > 2
            assert res["gamma_t"] is None
            gamma = 3

        gap = 2 * len(res["center"]) - gamma * res["M"]
        assert gap == t - 4
        if t == 5:
            assert n == 11 and res["m"] == 20 and len(res["center"]) == 11
            assert res["M"] == 7 and gamma == 3 and res["min_count"] == 5
            assert gamma * res["M"] == 21 < 22 == 2 * len(res["center"])
        print(
            f"  t={t:2d}: n={n:2d}, |E|={res['m']:3d}, |C|={len(res['center']):2d}, "
            f"M={res['M']:2d}, gamma_t={gamma}, gamma_t*M={gamma*res['M']:2d}, "
            f"2|C|={2*len(res['center']):2d}, 2|C|-gamma_t*M={gap:+d}"
            + (f" (min_sets={res['min_count']})" if t == 5 else "")
        )


def verify_rook_apex():
    print("\n=== 2. Rook-Group-Apex Family H_k (k = 2, 3, 4) ===")
    for k in (2, 3, 4):
        q = k * k
        # 0 = apex x; 1..k = h_0..h_{k-1}; k+1 .. k+q*q = grid (r, c)
        def gid(r, c):
            return 1 + k + r * q + c

        n = 1 + k + q * q
        edges = []
        # Rook edges on q x q grid
        for r in range(q):
            for c1 in range(q):
                for c2 in range(c1 + 1, q):
                    edges.append((gid(r, c1), gid(r, c2)))
        for c in range(q):
            for r1 in range(q):
                for r2 in range(r1 + 1, q):
                    edges.append((gid(r1, c), gid(r2, c)))
        # Group vertices h_g connected to rows g*k .. (g+1)*k - 1
        for g in range(k):
            edges.append((0, 1 + g))
            for r in range(g * k, (g + 1) * k):
                for c in range(q):
                    edges.append((1 + g, gid(r, c)))

        res = analyze_graph(n, edges, check_gamma_up_to=None)
        assert set(res["ecc"]) == {2}
        assert len(res["center"]) == k**4 + k + 1
        assert len(res["N"][0]) == k
        for g in range(k):
            assert len(res["N"][1 + g]) == k**3 + 1
        for r in range(q):
            for c in range(q):
                assert len(res["N"][gid(r, c)]) == 2 * k**2 - 1

        # Explicit total dominating set {0, 1, ..., k} of size k + 1
        D = set(range(k + 1))
        assert all(res["N"][v] & D for v in range(n))
        upper = (k + 1) * res["M"]
        assert res["M"] <= k**3 + 2 * k**2
        ratio = upper / len(res["center"])
        print(
            f"  k={k}: n=|C|={n:3d}, |E|={res['m']:4d}, M={res['M']:3d} "
            f"(<= {k**3 + 2*k**2}), gamma_t <= {k+1}, "
            f"(k+1)*M/|C| = {ratio:.6f}"
        )


def verify_exhaustive_small():
    print("\n=== 3. Exhaustive Verification for All Connected Graphs (2 <= n <= 6) ===")
    total_connected = 0
    for n in range(2, 7):
        all_pairs = list(combinations(range(n), 2))
        m_pairs = len(all_pairs)
        conn_count = 0
        min_margin = None
        for mask in range(1, 1 << m_pairs):
            # Build adjacency bitmasks
            adj = [0] * n
            edges = []
            for idx, (u, v) in enumerate(all_pairs):
                if (mask >> idx) & 1:
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
                    edges.append((u, v))
            # Quick BFS connectivity from 0 using bitmasks
            seen = 1
            frontier = 1
            while frontier:
                nxt = 0
                f = frontier
                while f:
                    lsb = f & -f
                    u = lsb.bit_length() - 1
                    nxt |= adj[u]
                    f ^= lsb
                nxt &= ~seen
                seen |= nxt
                frontier = nxt
            if seen != (1 << n) - 1:
                continue
            conn_count += 1

            # Eccentricities via bitmask BFS
            ecc = [0] * n
            for s in range(n):
                s_seen = 1 << s
                s_front = s_seen
                d = 0
                while s_seen != (1 << n) - 1:
                    d += 1
                    nxt = 0
                    f = s_front
                    while f:
                        lsb = f & -f
                        u = lsb.bit_length() - 1
                        nxt |= adj[u]
                        f ^= lsb
                    nxt &= ~s_seen
                    s_seen |= nxt
                    s_front = nxt
                ecc[s] = d
            c_size = ecc.count(min(ecc))
            M = max((adj[u] | adj[v]).bit_count() for u, v in edges)

            # Minimal total dominating set size
            all_mask = (1 << n) - 1
            gamma_t = None
            for sz in range(2, n + 1):
                found = False
                for comb in combinations(range(n), sz):
                    cov = 0
                    for v in comb:
                        cov |= adj[v]
                    if cov == all_mask:
                        found = True
                        break
                if found:
                    gamma_t = sz
                    break
            assert gamma_t is not None
            margin = gamma_t * M - 2 * c_size
            assert margin >= 0, f"Counterexample found on n={n}: {edges}"
            if min_margin is None or margin < min_margin:
                min_margin = margin
        assert conn_count == {2: 1, 3: 4, 4: 38, 5: 728, 6: 26704}[n]
        total_connected += conn_count
        print(f"  n={n}: checked all {conn_count:5d} connected labeled graphs -> min(gamma_t*M - 2|C|) = {min_margin} (>= 0)")
    print(f"  Total connected labeled graphs checked (2 <= n <= 6): {total_connected}")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O or -OO so verification assertions are enabled.")
    verify_subdivided_clique()
    verify_rook_apex()
    verify_exhaustive_small()
    print("\nALL VERIFICATIONS PASSED.")
