"""Full 128-point computation using an integer Walsh transform."""

from __future__ import annotations

from functools import cache

import numpy as np


N_FUNCTIONS = 1 << 12
N_POINTS = 1 << 7


def t_action(value: int) -> int:
    a0 = value & 1
    a1 = (value >> 1) & 1
    b0 = (value >> 2) & 1
    b1 = (value >> 3) & 1
    c0 = (value >> 4) & 1
    c1 = (value >> 5) & 1
    c2 = (value >> 6) & 1

    na0, na1 = a1, a0 ^ a1
    nb0, nb1 = b1, b0 ^ b1
    nc0, nc1, nc2 = c2, c0 ^ c2, c1

    return (
        na0
        | (na1 << 1)
        | (nb0 << 2)
        | (nb1 << 3)
        | (nc0 << 4)
        | (nc1 << 5)
        | (nc2 << 6)
    )


def action_orbits() -> list[list[int]]:
    unseen = set(range(N_POINTS))
    orbits: list[list[int]] = []
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


def translate_mask(mask: int, translation: int) -> int:
    translated = 0
    for point in range(N_POINTS):
        if mask & (1 << (point ^ translation)):
            translated |= 1 << point
    return translated


def orbit_masks() -> list[int]:
    masks = []
    for orbit in action_orbits():
        mask = 0
        for point in orbit:
            mask |= 1 << point
        masks.append(mask)
    return masks


def linear_map_rows() -> np.ndarray:
    basis = orbit_masks()
    rows = np.zeros((N_POINTS, 12), dtype=np.uint16)
    translated_basis = [
        [translate_mask(mask, translation) for mask in basis]
        for translation in range(N_POINTS)
    ]

    for translation in range(N_POINTS):
        for output_orbit, output_mask in enumerate(basis):
            input_mask = 0
            for input_orbit in range(12):
                if (translated_basis[translation][input_orbit] & output_mask).bit_count() & 1:
                    input_mask |= 1 << input_orbit
            rows[translation, output_orbit] = input_mask
    return rows


def fwht_in_place(values: np.ndarray) -> None:
    width = 1
    while width < values.shape[1]:
        blocks = values.reshape(values.shape[0], -1, 2 * width)
        left = blocks[:, :, :width].copy()
        right = blocks[:, :, width:].copy()
        blocks[:, :, :width] = left + right
        blocks[:, :, width:] = left - right
        width *= 2


@cache
def zero_free_statuses() -> np.ndarray:
    """Return the zero-free status for every 12-bit A-fixed function."""
    rows = linear_map_rows()
    all_u = np.arange(N_FUNCTIONS, dtype=np.uint16)
    parity = np.array([value.bit_count() & 1 for value in range(N_FUNCTIONS)], dtype=np.uint8)
    frequencies = np.zeros((N_FUNCTIONS, N_FUNCTIONS), dtype=np.int16)
    row_indices = np.arange(N_FUNCTIONS)

    for translation in range(N_POINTS):
        functional = np.zeros(N_FUNCTIONS, dtype=np.uint16)
        for output_bit in range(12):
            functional |= (
                parity[np.bitwise_and(all_u, rows[translation, output_bit])].astype(np.uint16)
                << output_bit
            )
        np.add.at(frequencies, (row_indices, functional), 1)

    fwht_in_place(frequencies)
    return np.all(frequencies != 0, axis=1)


def count_characters() -> tuple[int, int]:
    zero_free = int(np.count_nonzero(zero_free_statuses()))
    return zero_free, N_FUNCTIONS - zero_free


if __name__ == "__main__":
    zero_free, has_zero = count_characters()
    print(f"zero-free: {zero_free}")
    print(f"has a zero: {has_zero}")
