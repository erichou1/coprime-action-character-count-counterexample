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
from verification.design_search import (
    balanced_submultisets,
    is_prime,
    orbit_sizes as design_orbit_sizes,
    search,
    small_table,
)
from verification.linear_criterion import popcount
from verification.carter_subgroup import (
    carter_order,
    count_nonvanishing,
    inner_product_on_K,
    values_on_K,
)

EXPECTED = (1728, 2368)
ORBIT_SIZES = [1, 3, 3, 3, 3, 3, 7, 21, 21, 21, 21, 21]


def test_linear_criterion_count():
    assert count_linear() == EXPECTED


def test_direct_field_count():
    assert count_direct() == EXPECTED


def test_walsh_transform_count():
    assert count_walsh() == EXPECTED


def test_direct_field_orbit_sizes():
    assert orbit_sizes() == ORBIT_SIZES


def test_explicit_witness():
    assert verify_explicit_witness() == 0


def test_design_table_matches_manuscript():
    """The table in the proposition on the smallest admissible design."""
    expected = {
        (4, 15, (15,)): False,
        (5, 21, (3, 7)): False,
        (6, 15, (3, 5)): False,
        (6, 15, (3, 15)): False,
        (6, 21, (21,)): False,
        (6, 63, (63,)): False,
        (7, 21, (3, 3, 7)): True,
        (7, 35, (5, 7)): False,
        (7, 93, (3, 31)): False,
        (7, 105, (7, 15)): False,
    }
    actual = {(dim, m, orders): ok for dim, m, orders, _, ok in small_table()}
    assert actual == expected


def test_design_orbit_sizes_agree_with_the_field_computation():
    assert design_orbit_sizes((3, 3, 7)) == ORBIT_SIZES


def test_twenty_balanced_submultisets():
    """The twenty A-stable subsets of V of size 64."""
    assert balanced_submultisets(ORBIT_SIZES, 64) == 20


def test_smallest_admissible_design_is_the_one_used():
    admissible = search()
    assert len(admissible) == 53
    dim, m, orders, sizes, _ = admissible[0]
    assert (dim, m, orders) == (7, 21, (3, 3, 7))
    assert sizes == ORBIT_SIZES
    # next-smallest, quoted in the remark after the proposition
    assert admissible[1][:3] == (8, 15, (3, 3, 5))


def test_no_admissible_design_has_prime_order_operator_group():
    """The proposition ruling out |A| prime."""
    assert not any(is_prime(m) for _, m, _, _, _ in search())


def test_no_balanced_pair_in_dimension_at_most_five():
    """Subgroup enumeration covering all odd-order A with dim V <= 5."""
    from verification.noncyclic_search import run

    assert run(5) == []


def test_support_sum_criterion_matches_the_theorem():
    """The arithmetic half of the dimension-six theorem: nothing feasible
    below dimension 7, and at dimension 7 exactly the shapes containing
    the example's (2,2,3) with d=(3,3,7) pass."""
    from verification.scalar_obstruction import search

    assert search(6) == []
    at_seven = search(7)
    assert (7, (2, 2, 3), (3, 3, 7)) in at_seven
    assert all(n == 7 for n, _, _ in at_seven)


def test_balanced_is_closed_under_adding_a_fixed_point_free_summand():
    """The proposition giving infinitely many balanced pairs: if (A,V) is
    balanced and V' is fixed-point-free, then (A, V (+) V') is balanced."""
    from verification.design_search import is_balanced, orbit_sizes

    base = (3, 3, 7)  # V = F_4 (+) F_4 (+) F_8, the smallest balanced pair
    assert is_balanced(orbit_sizes(base), 1 << 6)
    for extra in [(3,), (7,), (3, 3), (3, 7), (21,)]:
        orders = tuple(sorted(base + extra))
        sizes = orbit_sizes(orders)
        assert is_balanced(sizes, sum(sizes) // 2), orders


def test_carter_subgroup_count():
    """Problem 6.7: 36288 characters of Gamma nonvanishing on K, |K/K'| = 86016."""
    assert count_nonvanishing() == 36288
    assert carter_order() == 86016


def test_carter_reduces_to_main_count_at_k_zero():
    """The k = 0 condition alone is exactly membership in N_A(G)."""
    base = sum(bool((values_on_K(b)[0] != 0).all()) for b in range(4096))
    assert base == 1728


def test_restriction_to_K_is_a_character():
    """<chi_K, chi_K> must be a positive integer; checks the transversal
    formula.  inner_product_on_K computes it in exact integer arithmetic
    and raises if any division fails to be exact."""
    for bits in range(0, 4096, 97):
        assert inner_product_on_K(bits) >= 1


def correlation_formula(x_value: int, e_value: int) -> int:
    x0 = x_value & 1
    e0 = e_value & 1
    x = (x_value >> 1) & 0b11111
    e = (e_value >> 1) & 0b11111
    sx = popcount(x) & 1
    se = popcount(e) & 1
    dot = popcount(x & e) & 1
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
