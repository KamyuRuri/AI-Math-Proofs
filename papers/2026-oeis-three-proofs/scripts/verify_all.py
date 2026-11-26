#!/usr/bin/env python3
"""
Independent exact-arithmetic verification of all three OEIS proofs:
  1. A352834: subpolynomial growth bound + global extremum at (n, a(n)) = (154440, 840)
  2. A304362: worked example b(2^36 * 3^21 * 5^15) = -4 + Fermat-CRT construction for +/- r
  3. A174013: quadratic identity, square-root-free ODE, 6th-order and 7th-order recurrences
"""

from fractions import Fraction
from itertools import product
from math import gcd, prod


def divisor_count(m: int) -> int:
    assert m >= 1
    p, result = 2, 1
    while p * p <= m:
        e = 0
        while m % p == 0:
            e += 1
            m //= p
        result *= e + 1
        p = 3 if p == 2 else p + 2
    return result * (2 if m > 1 else 1)


def moebius(n: int) -> int:
    assert n >= 1
    p = 2
    cnt = 0
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            cnt += 1
        p = 3 if p == 2 else p + 2
    if n > 1:
        cnt += 1
    return -1 if cnt % 2 else 1


def verify_a352834():
    print("=== Verifying A352834 ===")
    primes = (2, 3, 5, 7, 11, 13, 17, 19)
    target = Fraction(840**3, 154440)
    assert target == Fraction(548800, 143)

    def factor_score(p: int, e: int) -> Fraction:
        return Fraction((e + 1) ** 4, p**e)

    def peak(p: int) -> tuple[int, Fraction]:
        e = 0
        while factor_score(p, e + 1) > factor_score(p, e):
            e += 1
        return e, factor_score(p, e)

    peaks = {p: peak(p) for p in primes}
    for p in primes:
        e_peak, m_p = peaks[p]
        print(f"  p={p:2d}: peak e={e_peak}, M_p={m_p} ({float(m_p):.6f})")

    bound = prod(m_p for _, m_p in peaks.values())
    print(f"  Global bound B = {bound} = {float(bound):.8f}")
    print(f"  Target T = {target} = {float(target):.8f}")
    print(f"  B/16 = {float(bound / 16):.8f} < T")
    print(f"  16*B/23 = {float(16 * bound / 23):.8f} < T")
    assert bound / 16 < target
    assert 16 * bound / 23 < target

    def allowed_exponents(p: int) -> list[int]:
        other_max = bound / peaks[p][1]
        res = []
        e = 0
        while True:
            val = factor_score(p, e)
            if val * other_max >= target:
                res.append(e)
            elif factor_score(p, e + 1) <= val:
                return res
            e += 1

    ranges = [allowed_exponents(p) for p in primes]
    for p, r in zip(primes, ranges):
        print(f"  Allowed e_{p}: {r}")
    assert prod(len(r) for r in ranges) == 240

    above = 0
    integral_rows = []
    winners = []

    for exps in product(*ranges):
        m = prod(p**e for p, e in zip(primes, exps))
        d = prod(e + 1 for e in exps)
        h_val = Fraction(d**4, m)
        if h_val < target:
            continue
        above += 1
        if m % d != 0:
            continue
        n = m // d
        k = next(
            j for j in range(1, d + 1) if gcd(divisor_count(j * n), j * n) == j
        )
        ratio_cubed = Fraction(k**3, n)
        integral_rows.append((exps, m, d, n, k, ratio_cubed))
        if ratio_cubed >= target:
            winners.append((n, k))

    assert above == 57
    assert len(integral_rows) == 21
    assert winners == [(154440, 840)]
    print(f"  Summary: 240 box -> {above} with H(m)>=T -> {len(integral_rows)} with tau(m)|m -> winner {winners}")
    print("  All 21 integral candidates (sorted by k^3/n desc):")
    for idx, (exps, m, d, n, k, rc) in enumerate(
        sorted(integral_rows, key=lambda r: r[5], reverse=True), 1
    ):
        print(
            f"    {idx:2d}. e={exps} m={m} tau={d} n={n} a(n)={k} "
            f"(k^3/n={float(rc):.6f}, (k/n^(1/3))={float(rc)**(1/3):.6f})"
        )


def b304362_from_exponents(exps: tuple[int, ...]) -> int:
    """Compute b(n) when n = prod p_i^{e_i} with all e_i >= 2 (so 1 has all exps 0)."""
    assert all(e >= 2 for e in exps)
    total = 0
    for bits in product((0, 1), repeat=len(exps)):
        mu = (-1) ** sum(bits)
        d_exps = [e - b for e, b in zip(exps, bits)]
        g = 0
        for de in d_exps:
            g = gcd(g, de)
        is_perfect_power = g >= 2
        if not is_perfect_power:
            total += mu
    return total


def verify_a304362():
    print("\n=== Verifying A304362 ===")
    # Explicit brute-force divisor sum for n = 2^36 * 3^21 * 5^15? No, too many divisors;
    # check smaller exponents and check subset-sum equivalence, plus verify 2^36 * 3^21 * 5^15 via squarefree n/d.
    val_example = b304362_from_exponents((36, 21, 15))
    print(f"  b(2^36 * 3^21 * 5^15) = {val_example}")
    assert val_example == -4

    # Verify brute-force divisor definition matches exponent formula on small numbers
    def is_perfect_power(d: int) -> bool:
        if d < 4:
            return False
        s = 2
        while (1 << s) <= d:
            u = round(d ** (1.0 / s))
            for cand in (u - 1, u, u + 1):
                if cand >= 2 and cand**s == d:
                    return True
            s += 1
        return False

    def b_direct(n: int) -> int:
        res = 0
        for d in range(1, n + 1):
            if n % d == 0 and (d == 1 or not is_perfect_power(d)):
                res += moebius(n // d)
        return res

    # Test prime values
    for p in (2, 3, 5, 7, 11):
        assert b_direct(p) == 0

    # Test small composite with all exponents >= 2
    assert b_direct(2**2 * 3**2) == b304362_from_exponents((2, 2))
    assert b_direct(2**4 * 3**3 * 5**2) == b304362_from_exponents((4, 3, 2))

    # Verify explicit Fermat-CRT construction u_i = Q_i^(q_i - 1) + Q for r = 1, 2, 3, 4
    first_primes = [2, 3, 5, 7, 11]
    for r in range(1, 5):
        qs = first_primes[:r]
        Q = prod(qs)
        us = []
        for i, q in enumerate(qs):
            Q_i = prod(qs[j] for j in range(r) if j != i)
            u_i = Q_i ** (q - 1) + Q
            assert u_i >= 2
            assert (u_i - 1) % q == 0 and u_i % q != 0
            for j, qj in enumerate(qs):
                if j != i:
                    assert u_i % qj == 0 and (u_i - 1) % qj != 0
            us.append(u_i)
        assert gcd(Q - 1, 2 * Q) == 1
        assert gcd(Q, 2 * Q - 1) == 1
        assert gcd(Q - 1, 2 * Q - 1) == 1
        exps_pos = (Q, 2 * Q, *us)
        exps_neg = (Q, 2 * Q, *us, Q + 1)
        b_pos = b304362_from_exponents(exps_pos)
        b_neg = b304362_from_exponents(exps_neg)
        print(f"  r={r}: exps_pos={exps_pos} -> b={b_pos}; exps_neg={exps_neg} -> b={b_neg}")
        assert b_pos == r
        assert b_neg == -r


def verify_a174013():
    print("\n=== Verifying A174013 ===")

    def poly_sub(a, b):
        n = max(len(a), len(b))
        return [(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)]

    def poly_mul(a, b):
        res = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                res[i + j] += x * y
        return res

    def poly_deriv(a):
        return [i * a[i] for i in range(1, len(a))]

    B = [0, 2, -2, -2]
    H = [1, -3, -1]
    D = [1, -2, -1, 6, 5]

    # Verify H^2 - D = -2(1-x)B
    lhs = poly_sub(poly_mul(H, H), D)
    rhs = poly_mul([-2, 2], B)
    assert lhs[:5] == rhs[:5] and all(c == 0 for c in lhs[5:] + rhs[5:])

    Bp, Hp, Dp = poly_deriv(B), poly_deriv(H), poly_deriv(D)
    P = poly_mul([2], poly_mul(D, B))
    Q = poly_sub(poly_mul([2], poly_mul(D, Bp)), poly_mul(Dp, B))
    R = poly_sub(poly_mul(Dp, H), poly_mul([2], poly_mul(D, Hp)))

    assert all(c % 4 == 0 for c in P + Q + R)
    P4 = [c // 4 for c in P]
    Q4 = [c // 4 for c in Q]
    R4 = [c // 4 for c in R]
    print(f"  P/4 = {P4}")
    print(f"  Q/4 = {Q4}")
    print(f"  R/4 = {R4}")
    assert P4 == [0, 1, -3, 0, 9, 0, -11, -5]
    assert Q4 == [1, -3, 0, 3, -6, -9, -5]
    assert R4 == [1, -1, 3, 0, -6, 0]

    # Compute integer coefficients a_n up to n=40 from quadratic equation
    # x(1-x-x^2) A^2 + (1-3x-x^2) A - (1-x) = 0
    N = 41
    a = [0] * N
    a[0] = 1
    for n in range(1, N):
        # Coeff of x^n in (1-3x-x^2)A is a_n - 3 a_{n-1} - a_{n-2}
        # Coeff of x^n in x(1-x-x^2)A^2 is c_{n-1} - c_{n-2} - c_{n-3}, where c_m = sum_{i+j=m} a_i a_j
        c = lambda m: sum(a[i] * a[m - i] for i in range(m + 1)) if m >= 0 else 0
        rhs_const = -1 if n == 1 else 0
        quad_term = c(n - 1) - (c(n - 2) if n >= 2 else 0) - (c(n - 3) if n >= 3 else 0)
        lin_prev = 3 * a[n - 1] + (a[n - 2] if n >= 2 else 0)
        a[n] = rhs_const + lin_prev - quad_term

    print(f"  First 15 terms: {a[:15]}")
    assert a[:14] == [1, 1, 3, 6, 12, 22, 37, 56, 73, 75, 44, -21, -39, 297]

    def get(i: int) -> int:
        return a[i] if i >= 0 else 0

    def E(n: int) -> int:
        return (
            (n + 1) * get(n)
            - 3 * n * get(n - 1)
            + (9 * n - 24) * get(n - 3)
            - 6 * get(n - 4)
            + (46 - 11 * n) * get(n - 5)
            + (25 - 5 * n) * get(n - 6)
        )

    def M(n: int) -> int:
        return (
            (n + 1) * get(n)
            + n * get(n - 1)
            + 12 * (1 - n) * get(n - 2)
            + (9 * n - 24) * get(n - 3)
            + (36 * n - 138) * get(n - 4)
            + (22 - 11 * n) * get(n - 5)
            + (253 - 49 * n) * get(n - 6)
            + (120 - 20 * n) * get(n - 7)
        )

    assert [E(n) for n in range(5)] == [1, -1, 3, 0, -6]
    for n in range(5, N):
        assert E(n) == 0, f"E({n}) = {E(n)}"
    for n in range(6, N):
        assert M(n) == E(n) + 4 * E(n - 1) == 0, f"M({n}) = {M(n)}"
    print("  Verified E_n = 0 for 5 <= n <= 40 and Mathar's M_n = 0 for 6 <= n <= 40.")


if __name__ == "__main__":
    verify_a352834()
    verify_a304362()
    verify_a174013()
    print("\nALL VERIFICATIONS PASSED.")
