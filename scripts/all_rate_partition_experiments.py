"""Exact regression checks for the simplex/partition bridge; no network or file I/O.

These finite tests illustrate the Lean proofs; they do not replace uniform verification.
"""

from collections import Counter
from fractions import Fraction
from math import ceil, comb, factorial, exp, log, prod


def simplex(r, budget):
    if r == 0:
        yield ()
    else:
        for x in range(budget + 1):
            for tail in simplex(r - 1, budget - x):
                yield (x,) + tail


def partition_gaps(u):
    ordered = sorted(u, reverse=True) + [0]
    return tuple(ordered[i] - ordered[i + 1] for i in range(len(u)))


def max_le_count(r, budget, cap):
    if cap < 0:
        return 0
    return sum((-1) ** j * comb(r, j) * comb(budget - j * (cap + 1) + r, r)
               for j in range(r + 1) if j * (cap + 1) <= budget)


def exact_checks():
    assert partition_gaps(()) == ()
    assert max_le_count(0, 0, 0) == 1
    instances = bands = points = 0
    for r in range(1, 6):
        for budget in range(13):
            vectors = list(simplex(r, budget))
            fibers = Counter(partition_gaps(u) for u in vectors)
            assert len(vectors) == comb(budget + r, r)
            for u in vectors:
                c = partition_gaps(u)
                assert sum((j + 1) * x for j, x in enumerate(c)) == sum(u)
                assert sum(c) == max(u)
            assert max(fibers.values()) <= factorial(r)
            for cap in range(budget + 1):
                assert max_le_count(r, budget, cap) == sum(max(u) <= cap for u in vectors)
            for lower in range(budget + 1):
                for upper in range(lower, budget + 1):
                    event = max_le_count(r, budget, upper) - max_le_count(r, budget, lower - 1)
                    band = sum(lower <= sum(c) <= upper for c in fibers)
                    assert event <= factorial(r) * band
                    bands += 1
                if lower > 0:
                    p = Fraction(comb(budget - lower + r, r), len(vectors))
                    p2 = (Fraction(comb(budget - 2 * lower + r, r), len(vectors))
                          if 2 * lower <= budget else Fraction(0))
                    assert p2 <= p * p
                    mu = r * p
                    actual = Fraction(sum(max(u) >= lower for u in vectors), len(vectors))
                    assert actual >= mu / (1 + mu)
            instances += 1
            points += len(vectors)
    print('exact combinatorial checks:', instances, 'simplexes,', points, 'points,', bands, 'bands')


def scalar_checks():
    c = Fraction(23, 4)
    lower_log_mu = Fraction(3, 5) * c - 1 - Fraction(1, 100)
    upper_tail_exponent = Fraction(1, 2) + Fraction(3, 20) * c - Fraction(1, 100)
    assert lower_log_mu == Fraction(61, 25)
    assert upper_tail_exponent == Fraction(541, 400)
    mass = Fraction(11, 12) - Fraction(13, 50)
    rank = Fraction(9, 8) * Fraction(20, 13) * Fraction(101, 100) * Fraction(19, 10)
    assert mass > Fraction(13, 20)
    assert rank < Fraction(10, 3)
    assert 162 * Fraction(10, 3) == 540
    print('candidate c=', c, 'mass floor=', mass, 'rank coefficient=', rank)
    print('numerical exponential checks (Lean proofs separately):',
          exp(float(lower_log_mu)), exp(float(upper_tail_exponent)),
          float(c * c) * exp(float(c / 2)))


def exact_tail_checks():
    pairs = 0
    for r in range(6):
        for budget in range(13):
            def p(t):
                return (Fraction(comb(budget - t + r, r), comb(budget + r, r))
                        if t <= budget else Fraction(0))

            for t in range(budget + 1):
                assert p(t) == prod(1 - Fraction(t, budget + i + 1) for i in range(r))
                assert (1 - Fraction(t, budget + 1)) ** r <= p(t)
            for s in range(budget + 2):
                for t in range(budget + 2):
                    assert p(s + t) <= p(s) * p(t)
                    pairs += 1
    # This guards against a spurious point from truncated natural subtraction.
    assert comb(max(2 - 3, 0) + 3, 3) == 1
    print('exact tail-product and correlation checks:', pairs, 'threshold pairs')


def illustrative_sizes():
    for gap in (0.24, 0.1, 0.05, 0.01):
        row = []
        for c in (6.76, 5.5):
            log_d = c / gap
            log_n = log(800) + 2 * log_d + log(log_d + 0.5772156649015329)
            row.append((round(log_d / log(10), 3), round(log_n / log(10), 3)))
        print('gap / approximate (log10 d, log10 N), original and verified refinement:', gap, row)


def dimension_slack_checks():
    theta = Fraction(17499, 50000)
    beta = Fraction(13, 20)
    assert 1 - beta - theta == Fraction(1, 50000)
    assert theta**3 / 6 >= Fraction(1, 140)
    assert Fraction(162, 140) == Fraction(81, 70)
    instances = 0
    for g in (Fraction(1), Fraction(1, 2), Fraction(1, 7),
              Fraction(1, 100), Fraction(1, 100003)):
        for offset in (0, 1, 7, 101):
            m = ceil(100000 / g) + offset
            upper = ceil((1 + beta * g) * m)
            side = ceil(theta * g * m)
            assert (1 - beta - theta) * g * m >= 2
            assert side <= m + 1
            for degree in (1, 2, 7):
                budget = degree * m * (1 + g)
                assert degree * (upper + side) <= ceil(budget)
                simplex_count = side * (side + 1) * (side + 2) // 6
                assert degree * simplex_count >= degree * m**3 * g**3 / 140
                instances += 1
    # Ignoring the ceiling reserve already fails at g=m=D=1.
    assert ceil(1 + beta) + ceil(1 - beta) > ceil(Fraction(2))
    assert Fraction(140) * Fraction(10, 3) == Fraction(1400, 3)
    c = Fraction(11, 2)
    # Rational Taylor polynomials, not floating point, certify all three margins.
    taylor = lambda x, terms: sum((x**i / factorial(i) for i in range(terms)), Fraction(0))
    assert c**2 * taylor(c / 2, 12) > Fraction(1400, 3)
    lower_exponent = Fraction(3, 5) * c - Fraction(3, 5) - Fraction(1, 100)
    upper_exponent = Fraction(1, 2) + Fraction(3, 20) * c - Fraction(1, 100)
    assert lower_exponent == Fraction(269, 100)
    assert upper_exponent == Fraction(263, 200)
    assert taylor(lower_exponent, 12) > 14
    assert taylor(upper_exponent, 10) > Fraction(100, 27)
    assert Fraction(14, 15) - Fraction(27, 100) > Fraction(13, 20)
    assert taylor(Fraction(22), 12) >= 1000000
    for offset in (Fraction(0), Fraction(1, 100), Fraction(1), Fraction(10), Fraction(1000)):
        assert 1000 * (offset + 23)**2 <= 1000000 * (1 + offset + offset**2 / 2)
    assert Fraction(1, 1000) / (1 - Fraction(1, 1000)) < Fraction(1, 100)
    assert 2 * Fraction(1, 1000) + 2 * Fraction(1, 1000) < Fraction(1, 100)
    print('exact dimension rounding checks:', instances, 'cases; c=11/2 scalar margins passed')


if __name__ == '__main__':
    exact_checks()
    exact_tail_checks()
    scalar_checks()
    dimension_slack_checks()
    illustrative_sizes()
