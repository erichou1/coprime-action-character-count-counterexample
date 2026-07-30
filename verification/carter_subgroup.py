"""Problem 6.7 for Gamma = G x| A and its Carter subgroup K = C x A.

Setting: G = B x| V and A as in the manuscript, Gamma = G x| A, and
K = C x A where C = C_G(A).  The manuscript shows K is a Carter subgroup
of Gamma, and that every chi in Irr(Gamma) nonvanishing on K lies over an
A-invariant theta in Irr(G); those chi are exactly theta-hat . lambda for
lambda in Irr(A), so 21 per theta.

Writing theta = chi_u for u in B^A, and letting a in A act on V as T^k,
a transversal computation gives

    chi(c, a) = lambda(a) * D_k(c),
    D_k(c)   = sum over t in S_k / V_u of (-1)^{<tau_t u, c>},
    S_k      = { t in V : (T^k + 1) t in V_u }.

Since |lambda(a)| = 1, vanishing does not depend on lambda.  Both V_u and
S_k are T-invariant and t -> <tau_t u, c> is constant on A-orbits, so
D_k(c) is a signed sum of the sizes of the A-orbits contained in S_k.

`count_nonvanishing()` returns the number of chi in Irr(Gamma) that are
nonvanishing on K.  `inner_product_on_K()` is an independent check on the
formula: <chi_K, chi_K> must be a positive integer for every chi.
"""

from __future__ import annotations

from functools import reduce, cache

import numpy as np

N_POINTS = 128
N_ORBITS = 12
ORDER_A = 21


def _mul(a: int, b: int, modulus: int, degree: int) -> int:
    result, x, y = 0, a, b
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x >> degree & 1:
            x ^= modulus
    return result & ((1 << degree) - 1)


def _mul4(a: int, b: int) -> int:
    return _mul(a, b, 0b111, 2)


def _mul8(a: int, b: int) -> int:
    return _mul(a, b, 0b1011, 3)


def popcount(value: int) -> int:
    return bin(value).count("1")


@cache
def _structure():
    points = [(x1, x2, y) for x1 in range(4) for x2 in range(4) for y in range(8)]
    index = {p: i for i, p in enumerate(points)}

    def act(p):
        return (_mul4(2, p[0]), _mul4(2, p[1]), _mul8(2, p[2]))

    # T^k as permutations of point indices
    powers, current = [], list(range(N_POINTS))
    for _ in range(ORDER_A):
        powers.append(current[:])
        current = [index[act(points[i])] for i in current]
    assert [index[act(points[i])] for i in powers[-1]] == list(range(N_POINTS))

    add = [
        [index[(points[i][0] ^ points[j][0],
                points[i][1] ^ points[j][1],
                points[i][2] ^ points[j][2])] for j in range(N_POINTS)]
        for i in range(N_POINTS)
    ]

    orbits, seen = [], set()
    for i in range(N_POINTS):
        if i in seen:
            continue
        orbit, j = [], i
        while j not in orbit:
            orbit.append(j)
            seen.add(j)
            j = index[act(points[j])]
        orbits.append(orbit)
    assert sorted(len(o) for o in orbits) == [1, 3, 3, 3, 3, 3, 7, 21, 21, 21, 21, 21]

    masks = [reduce(lambda m, p: m | 1 << p, o, 0) for o in orbits]
    return powers, add, orbits, masks


def _fixed_function(bits: int) -> int:
    """The element of B^A with the given 12-bit orbit pattern, as a mask."""
    _, _, _, masks = _structure()
    out = 0
    for j in range(N_ORBITS):
        if bits >> j & 1:
            out |= masks[j]
    return out


def _translate(mask: int, t: int) -> int:
    _, add, _, _ = _structure()
    out = 0
    for i in range(N_POINTS):
        if mask >> i & 1:
            out |= 1 << add[i][t]
    return out


@cache
def _walsh() -> np.ndarray:
    size = 1 << N_ORBITS
    parity = np.array([popcount(v) & 1 for v in range(size)], dtype=np.int8)
    grid = np.bitwise_and.outer(
        np.arange(size, dtype=np.uint16), np.arange(size, dtype=np.uint16)
    )
    return np.where(parity[grid] == 0, 1, -1).astype(np.int32)


def _data(u_bits: int):
    """Return (rows, coef, |V_u|) for the character indexed by u_bits."""
    powers, add, orbits, masks = _structure()
    u = _fixed_function(u_bits)
    translated = [_translate(u, t) for t in range(N_POINTS)]
    stabilizer = {t for t in range(N_POINTS) if translated[t] == u}

    phi = []
    for orbit in orbits:
        t = orbit[0]
        word = 0
        for j in range(N_ORBITS):
            if popcount(translated[t] & masks[j]) & 1:
                word |= 1 << j
        phi.append(word)
    rows = _walsh()[np.array(phi)]

    sizes = np.array([len(o) for o in orbits], dtype=np.int32)
    coef = np.zeros((ORDER_A, N_ORBITS), dtype=np.int32)
    for k in range(ORDER_A):
        for j, orbit in enumerate(orbits):
            t = orbit[0]
            if add[powers[k][t]][t] in stabilizer:
                coef[k, j] = sizes[j]
    return rows, coef, len(stabilizer)


def values_on_K(u_bits: int) -> np.ndarray:
    """Array of shape (21, 4096): |V_u| * D_k(c), indexed by (k, c)."""
    rows, coef, _ = _data(u_bits)
    return coef @ rows


def is_nonvanishing_on_K(u_bits: int) -> bool:
    return bool(np.all(values_on_K(u_bits) != 0))


def inner_product_on_K(u_bits: int) -> int:
    """<chi_K, chi_K>, computed exactly; raises if it is not an integer."""
    rows, coef, order = _data(u_bits)
    values = coef @ rows                    # |V_u| * D_k(c), all integers
    quotients, remainders = np.divmod(values, order)
    if remainders.any():
        raise ArithmeticError("character values not divisible by |V_u|")
    total = int(np.sum(quotients.astype(np.int64) ** 2))
    quotient, remainder = divmod(total, (1 << N_ORBITS) * ORDER_A)
    if remainder:
        raise ArithmeticError("<chi_K, chi_K> is not an integer")
    return quotient


def count_nonvanishing() -> int:
    """Number of chi in Irr(Gamma) that do not vanish anywhere on K."""
    good = sum(is_nonvanishing_on_K(b) for b in range(1 << N_ORBITS))
    return ORDER_A * good


def carter_order() -> int:
    """|K/K'| = |K|, since K is abelian."""
    return (1 << N_ORBITS) * ORDER_A


if __name__ == "__main__":
    # k = 0 alone is the condition of the main theorem, so it must give 1728
    base = sum(
        bool(np.all(values_on_K(b)[0] != 0)) for b in range(1 << N_ORBITS)
    )
    print(f"nonvanishing on C only (= |N_A(G)|): {base}")

    total = count_nonvanishing()
    print(f"nonvanishing on all of K           : {total // ORDER_A} characters of G")
    print()
    print(f"|Irr(Gamma)| nonvanishing on K     : {total}")
    print(f"|K/K'|                             : {carter_order()}")
    print(f"ratio                              : {total}/{carter_order()}")

    sampled = [inner_product_on_K(b) for b in range(0, 1 << N_ORBITS, 97)]
    assert all(value >= 1 for value in sampled)
    print(f"\ncheck: <chi_K,chi_K> is an exact positive integer for "
          f"{len(sampled)} sampled characters (min {min(sampled)}, max {max(sampled)})")
