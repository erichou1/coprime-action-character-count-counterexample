"""The support-sum criterion behind the theorem on dimensions <= 6.

The manuscript proves: for ANY finite group A of odd order acting on
V = F_2^n with C_V(A) = 0, each simple summand V_i of V carries an odd
divisor d_i >= 3 of every nonzero orbit size of the image of A on V_i.
The possible d_i depend only on n_i = dim V_i:

    n_i : 2    3    4         5     6                7
    d_i : 3    7    3,5,15    31    3,7,9,21,63     127

(For n_i = 6 the value 3 covers both the scalar case e = 2 and the
imprimitive 3-group case.)  An A-orbit with support S has size divisible
by lcm{d_i : i in S}, and the orbits of support S cover exactly
prod_{i in S}(2^{n_i} - 1) vectors.  Balance therefore requires

    2^{n-1} = alpha + sum_S y_S,   alpha in {0,1},
    y_S a multiple of lcm{d_i : i in S},
    y_S <= prod_{i in S}(2^{n_i} - 1).

`feasible(dims, dvec)` decides that condition.  `search(nmax)` checks
every partition of each n <= nmax into parts >= 2 and every admissible
d-vector.  For nmax = 6 nothing is feasible, which is the arithmetic
half of the theorem; at n = 7 the criterion is passed by the shape
(2, 2, 3) with d = (3, 3, 7) realized by the example in the paper.
"""

from __future__ import annotations

from itertools import product as iproduct
from math import gcd

D_LIST = {2: [3], 3: [7], 4: [3, 5, 15], 5: [31],
          6: [3, 7, 9, 21, 63], 7: [127]}


def lcm(values) -> int:
    result = 1
    for value in values:
        result = result * value // gcd(result, value)
    return result


def partitions(n: int, minpart: int = 2):
    if n == 0:
        yield ()
        return
    for part in range(minpart, n + 1):
        for rest in partitions(n - part, part):
            yield (part,) + rest


def feasible(dims, dvec) -> bool:
    """Can the necessary condition for balance be satisfied?"""
    n = sum(dims)
    target = 1 << (n - 1)
    r = len(dims)
    reachable = {0, 1}  # the contribution alpha of the zero vector
    for mask in range(1, 1 << r):
        support = [i for i in range(r) if mask >> i & 1]
        step = lcm(dvec[i] for i in support)
        capacity = 1
        for i in support:
            capacity *= (1 << dims[i]) - 1
        new = set()
        for base in reachable:
            amount = 0
            while base + amount <= target and amount <= capacity:
                new.add(base + amount)
                amount += step
        reachable = new
    return target in reachable


def search(nmax: int):
    """All (n, dims, dvec) passing the criterion, for n <= nmax."""
    hits = []
    for n in range(2, nmax + 1):
        for dims in partitions(n):
            for dvec in iproduct(*[D_LIST[d] for d in dims]):
                if feasible(dims, dvec):
                    hits.append((n, dims, dvec))
    return hits


if __name__ == "__main__":
    for n, dims, dvec in search(7):
        print(f"n={n}  dims={dims}  d={dvec}  passes the criterion")
    up_to_six = [h for h in search(6)]
    print(f"\nfeasible cases with n <= 6: {len(up_to_six)}")
