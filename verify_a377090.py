"""Recompute A377090 and certify its first logarithmic violation.

Run 'python3 verify_a377090.py' or 'python3 verify_a377090.py 370340 dump'.

Option 'dump' prints n and a(n) on stdout. Statistics and the earliest violation
of the proposed logarithmic inequality go to stderr. Primality uses exact
trial division, with repeated differences cached.
"""
from fractions import Fraction
from functools import lru_cache
from math import factorial, isqrt, log
import sys

def integer_of(rank):
    return (rank + 1) // 2 if rank % 2 else -(rank // 2)

@lru_cache(maxsize=None)
def prime(x):
    if x < 2 or x % 2 == 0:
        return x == 2
    return all(x % j for j in range(3, isqrt(x) + 1, 2))

def terms(limit):
    # Unvisited ranks are the increasing list holes followed by [fresh, infinity).
    holes = []
    fresh = 1
    previous = 0
    yield previous
    for _ in range(limit):
        for j, rank in enumerate(holes):
            candidate = integer_of(rank)
            if prime(abs(previous - candidate)):
                holes.pop(j)
                break
        else:
            while True:
                candidate = integer_of(fresh)
                fresh += 1
                if prime(abs(previous - candidate)):
                    break
                holes.append(fresh - 1)
        previous = candidate
        yield previous

def first_violation(earliest):
    # e lies in (lo,hi) by its Taylor series; after k=10, ratios are at most 1/11.
    lo = sum(Fraction(1, factorial(k)) for k in range(11))
    hi = lo + Fraction(1, 10 * factorial(10))
    failures = []
    for d, (n, a) in earliest.items():
        # d < 4 log(n+2) iff e**d < (n+2)**4.
        target = (n + 2)**4
        if hi**d < target:
            continue
        if lo**d >= target:
            failures.append((n, a, d))
        else:
            raise ArithmeticError(f"Taylor bounds inconclusive at {n}")
    return min(failures, default=None)

def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 370313
    dump = len(sys.argv) > 2 and sys.argv[2] == "dump"
    earliest = {}
    for n, a in enumerate(terms(N)):
        if dump:
            print(n, a)
        d = abs(2 * abs(a) - n)
        earliest.setdefault(d, (n, a))
    answer = first_violation(earliest)
    print(f"last ({N}, {a}); first logarithmic violation {answer}", file=sys.stderr)
    if answer:
        n, a, d = answer
        print(f"deviation {d/2}; bound {2*log(n+2):.12f}", file=sys.stderr)

if __name__ == "__main__":
    main()
