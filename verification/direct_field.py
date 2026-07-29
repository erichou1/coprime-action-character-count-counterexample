"""Direct computation with radial functions on F_4^2 and the F_8 slices."""

from __future__ import annotations

from functools import cache

import numpy as np


def field_multiply(a: int, b: int, modulus: int, degree: int) -> int:
    result = 0
    x = a
    y = b
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x & (1 << degree):
            x ^= modulus
    return result & ((1 << degree) - 1)


def multiply_f4(a: int, b: int) -> int:
    return field_multiply(a, b, 0b111, 2)


def multiply_f8(a: int, b: int) -> int:
    return field_multiply(a, b, 0b1011, 3)


def t_action(point: tuple[int, int, int]) -> tuple[int, int, int]:
    x1, x2, y = point
    return multiply_f4(2, x1), multiply_f4(2, x2), multiply_f8(2, y)


def v_points() -> list[tuple[int, int, int]]:
    return [(x1, x2, y) for x1 in range(4) for x2 in range(4) for y in range(8)]


def action_orbits(points: list[tuple[int, int, int]]) -> list[list[tuple[int, int, int]]]:
    unseen = set(points)
    orbits: list[list[tuple[int, int, int]]] = []
    while unseen:
        start = min(unseen)
        orbit = []
        current = start
        while current not in orbit:
            orbit.append(current)
            unseen.discard(current)
            current = t_action(current)
        orbits.append(orbit)
    return sorted(orbits, key=lambda orbit: (len(orbit), orbit[0]))


def orbit_sizes() -> list[int]:
    return sorted(len(orbit) for orbit in action_orbits(v_points()))


def u_orbits() -> list[list[tuple[int, int]]]:
    points = [(x1, x2) for x1 in range(4) for x2 in range(4)]
    unseen = set(points)
    orbits: list[list[tuple[int, int]]] = []
    while unseen:
        start = min(unseen)
        orbit = []
        current = start
        while current not in orbit:
            orbit.append(current)
            unseen.discard(current)
            current = multiply_f4(2, current[0]), multiply_f4(2, current[1])
        orbits.append(orbit)
    return sorted(orbits, key=lambda orbit: (len(orbit), orbit[0]))


@cache
def radial_correlation_table() -> np.ndarray:
    points = [(x1, x2) for x1 in range(4) for x2 in range(4)]
    index = {point: i for i, point in enumerate(points)}
    orbits = u_orbits()
    orbit_index = {point: j for j, orbit in enumerate(orbits) for point in orbit}
    representatives = [orbit[0] for orbit in orbits]

    radial = np.empty((64, 16), dtype=np.uint8)
    for mask in range(64):
        radial[mask] = [(mask >> orbit_index[point]) & 1 for point in points]

    table = np.zeros((64, 64), dtype=np.uint8)
    for x_mask in range(64):
        x_values = radial[x_mask]
        for e_mask in range(64):
            e_values = radial[e_mask]
            output = 0
            for orbit_id, shift in enumerate(representatives):
                total = 0
                for z in points:
                    shifted = (z[0] ^ shift[0], z[1] ^ shift[1])
                    total ^= int(x_values[index[shifted]] & e_values[index[z]])
                output |= total << orbit_id
            table[x_mask, e_mask] = output
    return table


def signed_orbit_sum(mask: int) -> int:
    value = -1 if mask & 1 else 1
    for bit in range(1, 6):
        value += 3 * (-1 if mask & (1 << bit) else 1)
    return value


def character_has_zero(x_mask: int, y_mask: int) -> bool:
    """Return whether the character indexed by (X,Y) has a zero on C."""
    if not 0 <= x_mask < 64 or not 0 <= y_mask < 64:
        raise ValueError("X and Y must be six-bit integers")

    correlation = radial_correlation_table()
    signed_sum = np.array([signed_orbit_sum(mask) for mask in range(64)], dtype=np.int16)
    e_values = np.repeat(np.arange(64, dtype=np.uint8), 64)
    f_values = np.tile(np.arange(64, dtype=np.uint8), 64)

    h0 = correlation[x_mask, e_values] ^ correlation[y_mask, f_values]
    h1 = correlation[y_mask, e_values] ^ correlation[x_mask, f_values]
    character_values = signed_sum[h0] + 7 * signed_sum[h1]
    return bool(np.any(character_values == 0))


def count_characters() -> tuple[int, int]:
    zero_free = 0
    for x_mask in range(64):
        for y_mask in range(64):
            if not character_has_zero(x_mask, y_mask):
                zero_free += 1

    return zero_free, 4096 - zero_free


def verify_explicit_witness() -> int:
    orbits = action_orbits(v_points())
    product_orbits = [orbit for orbit in orbits if len(orbit) == 21]
    support = {(0, 0, 0)}
    for orbit in product_orbits[:3]:
        support.update(orbit)
    return sum(-1 if point in support else 1 for point in v_points())


if __name__ == "__main__":
    zero_free, has_zero = count_characters()
    print(f"orbit sizes: {orbit_sizes()}")
    print(f"explicit witness value: {verify_explicit_witness()}")
    print(f"zero-free: {zero_free}")
    print(f"has a zero: {has_zero}")
