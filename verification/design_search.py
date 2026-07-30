"""Enumeration of the design space behind the choice of V.

The manuscript reduces the existence of a vanishing invariant character
in the family G = F_2^V (x) V to a subset-sum condition on the multiset
of A-orbit sizes on V (the "balance condition"):

    some sub-multiset of the A-orbit sizes on V sums to |V|/2.

For A = C_m cyclic of odd order, V is a direct sum of irreducible
F_2[C_m]-modules, one for each divisor d | m; the module attached to d
has F_2-dimension ord_d(2) and the generator acts on it with order d.
Fixed-point-freeness excludes d = 1 and faithfulness requires
lcm{d_j} = m.  Orbit sizes are then read off from the module structure
by the lemma "orbit sizes from the module": the orbit of
v = (v_1, ..., v_r) has size lcm{d_j : v_j != 0}.

Nothing here builds a group.  The whole search happens on multisets of
divisors, so it is small enough to reproduce by hand -- which is how the
example in the manuscript was found.

Two entry points:

    small_table()   every candidate with dim V <= 7 (the table in the
                    proposition "smallest admissible design")
    search()        the wider machine search quoted in the remark that
                    follows it
"""

from __future__ import annotations

from itertools import combinations_with_replacement
from math import gcd


def order_mod(base: int, modulus: int) -> int | None:
    """Multiplicative order of `base` modulo `modulus`, or None."""
    if gcd(base, modulus) != 1:
        return None
    order, value = 1, base % modulus
    while value != 1:
        value = value * base % modulus
        order += 1
    return order


def lcm(values) -> int:
    result = 1
    for value in values:
        result = result * value // gcd(result, value)
    return result


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def is_prime_power(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            while n % d == 0:
                n //= d
            return n == 1
        d += 1
    return True  # n is prime


def orbit_sizes(orders: tuple[int, ...]) -> list[int]:
    """A-orbit sizes on V = (+)_j M_{d_j}, for d_j = orders[j]."""
    dims = [order_mod(2, d) for d in orders]
    sizes: list[int] = []
    for mask in range(1 << len(orders)):
        support = [j for j in range(len(orders)) if mask >> j & 1]
        if not support:
            sizes.append(1)  # the zero vector
            continue
        count = 1
        for j in support:
            count *= (1 << dims[j]) - 1
        size = lcm([orders[j] for j in support])
        assert count % size == 0
        sizes.extend([size] * (count // size))
    return sorted(sizes)


def is_balanced(sizes: list[int], target: int) -> bool:
    """Does some sub-multiset of `sizes` sum to exactly `target`?"""
    reachable = 1  # bitmask of attainable sums
    for size in sizes:
        reachable |= reachable << size
        reachable &= (1 << (target + 1)) - 1
    return bool(reachable >> target & 1)


def candidates(dim_max: int, m_max: int | None = None):
    """Yield (dim V, |A|, element orders, orbit sizes, balanced?).

    Ranges over every faithful fixed-point-free F_2[C_m]-module with
    m odd and dim V <= dim_max.  Iterating over m first keeps the
    enumeration small: the element orders must divide m, so each m
    contributes only multisets of its own divisors.
    """
    if m_max is None:
        # ord_d(2) <= dim_max forces d | 2^e - 1 for some e <= dim_max.
        m_max = (1 << dim_max) - 1
    for m in range(3, m_max + 1, 2):
        divs = [d for d in range(2, m + 1) if m % d == 0]
        dims = {d: order_mod(2, d) for d in divs}
        if any(v is None for v in dims.values()):
            continue  # m even, cannot happen here
        divs = [d for d in divs if dims[d] <= dim_max]
        if not divs:
            continue
        for size in range(1, dim_max // min(dims[d] for d in divs) + 1):
            for orders in combinations_with_replacement(divs, size):
                dim = sum(dims[d] for d in orders)
                if dim > dim_max:
                    continue
                if lcm(orders) != m:  # faithful, and avoids double counting
                    continue
                sizes = orbit_sizes(orders)
                assert sum(sizes) == 1 << dim
                yield dim, m, orders, sizes, is_balanced(sizes, 1 << (dim - 1))


def small_table() -> list[tuple]:
    """Every candidate with dim V <= 7 whose |A| is not a prime power,
    matching the table in the manuscript (prime powers are excluded
    there by the proposition on p-groups).

    The bound on |A| is far above what dim V <= 7 permits: every
    element order d satisfies ord_d(2) <= 7, hence d <= 127, and at
    most three summands fit, so |A| <= 105 in fact.
    """
    rows = [row for row in candidates(7, m_max=5000)
            if not is_prime_power(row[1])]
    return sorted(rows)


def search(dim_max: int = 14, m_max: int = 105) -> list[tuple]:
    """Every admissible design within the given bounds."""
    return sorted(row for row in candidates(dim_max, m_max) if row[4])


def balanced_submultisets(sizes: list[int], target: int) -> int:
    """Count sub-multisets summing to target, treating equal sizes as
    distinguishable (they index distinct orbits)."""
    counts = [1] + [0] * target
    for size in sizes:
        for total in range(target, size - 1, -1):
            counts[total] += counts[total - size]
    return counts[target]


if __name__ == "__main__":
    print("candidates with dim V <= 7, |A| not a prime power:")
    print(f"{'dim':>4} {'|A|':>5}  {'orders':<12} {'balanced':>8}  orbit sizes")
    for dim, m, orders, sizes, ok in small_table():
        print(f"{dim:>4} {m:>5}  {str(list(orders)):<12} {str(ok):>8}  {sizes}")

    admissible = search()
    print(f"\nadmissible designs with dim V <= 14, |A| <= 105: {len(admissible)}")
    dim, m, orders, sizes, _ = admissible[0]
    print(f"smallest: dim V = {dim}, |A| = {m}, element orders {list(orders)}")
    print(f"orbit sizes: {sizes}")
    print(
        f"sub-multisets summing to {1 << (dim - 1)}: "
        f"{balanced_submultisets(sizes, 1 << (dim - 1))}"
    )
    assert not any(is_prime_power(row[1]) for row in admissible)
    print("no admissible design has prime-power |A|")
