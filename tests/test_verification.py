from itertools import combinations

from verification.direct_field import character_has_zero as has_zero_direct
from verification.direct_field import count_characters as count_direct
from verification.direct_field import radial_correlation_table, signed_orbit_sum, u_orbits
from verification.linear_criterion import count_characters as count_linear
from verification.linear_criterion import character_has_zero as has_zero_linear
from verification.walsh_transform import action_orbits as full_action_orbits
from verification.walsh_transform import count_characters as count_walsh
from verification.walsh_transform import zero_free_statuses as walsh_zero_free_statuses
from verification.direct_field import orbit_sizes, verify_explicit_witness

EXPECTED = (1728, 2368)


def test_linear_criterion_count():
    assert count_linear() == EXPECTED


def test_direct_field_count():
    assert count_direct() == EXPECTED


def test_walsh_transform_count():
    assert count_walsh() == EXPECTED


def test_direct_field_orbit_sizes():
    assert orbit_sizes() == [1, 3, 3, 3, 3, 3, 7, 21, 21, 21, 21, 21]


def test_explicit_witness():
    assert verify_explicit_witness() == 0


def correlation_formula(x_value: int, e_value: int) -> int:
    x0 = x_value & 1
    e0 = e_value & 1
    x = (x_value >> 1) & 0b11111
    e = (e_value >> 1) & 0b11111
    sx = x.bit_count() & 1
    se = e.bit_count() & 1
    dot = (x & e).bit_count() & 1
    tau_x = x0 ^ sx
    tau_e = e0 ^ se

    output = x0 & e0 ^ dot
    common = sx & se ^ dot
    for bit in range(5):
        line_value = (
            (tau_e & ((x >> bit) & 1))
            ^ (tau_x & ((e >> bit) & 1))
            ^ common
        )
        output |= line_value << (bit + 1)
    return output


def test_correlation_formula_exhaustively():
    table = radial_correlation_table()
    for x_value in range(64):
        for e_value in range(64):
            assert int(table[x_value, e_value]) == correlation_formula(x_value, e_value)


def test_zero_patterns_are_exactly_the_twenty_claimed_patterns():
    actual = {
        (h0, h1)
        for h0 in range(64)
        for h1 in range(64)
        if signed_orbit_sum(h0) + 7 * signed_orbit_sum(h1) == 0
    }
    expected = set()
    for support in combinations(range(1, 6), 3):
        rho = sum(1 << bit for bit in support)
        expected.add((1, rho))
        expected.add((1 ^ 0b111111, rho ^ 0b111111))
    assert actual == expected


def test_direct_values_and_affine_criterion_agree_character_by_character():
    radial_index = {
        point: orbit_id
        for orbit_id, orbit in enumerate(u_orbits())
        for point in orbit
    }
    full_orbits = full_action_orbits()
    walsh_status = walsh_zero_free_statuses()

    for x_value in range(64):
        for y_value in range(64):
            p_value = x_value ^ y_value
            expected_has_zero = has_zero_linear(p_value, y_value)
            assert has_zero_direct(x_value, y_value) == expected_has_zero

            u_value = 0
            for orbit_id, orbit in enumerate(full_orbits):
                representative = orbit[0]
                x1 = representative & 0b11
                x2 = (representative >> 2) & 0b11
                w = (representative >> 4) & 0b111
                radial_bit = radial_index[(x1, x2)]
                slice_value = x_value if w == 0 else y_value
                u_value |= ((slice_value >> radial_bit) & 1) << orbit_id

            assert bool(walsh_status[u_value]) == (not expected_has_zero)
