"""Exact regression checks for the simplex/partition bridge; no network or file I/O.

These finite tests are not a proof of the proposed uniform 5.75 theorem.
"""

from collections import Counter
from fractions import Fraction
from math import comb, factorial, exp, log


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


def illustrative_sizes():
    for gap in (0.24, 0.1, 0.05, 0.01):
        row = []
        for c in (6.76, 5.75):
            log_d = c / gap
            log_n = log(800) + 2 * log_d + log(log_d + 0.5772156649015329)
            row.append((round(log_d / log(10), 3), round(log_n / log(10), 3)))
        print('gap / approximate (log10 d, log10 N), original and candidate:', gap, row)


if __name__ == '__main__':
    exact_checks()
    scalar_checks()
    illustrative_sizes()
