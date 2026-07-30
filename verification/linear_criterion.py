"""Enumeration using the complete zero criterion of the manuscript.

See the proposition "Complete zero criterion" in the section
"The exact zero criterion".
"""


def popcount(value: int) -> int:
    # int.bit_count() requires Python 3.10+; this works everywhere.
    return bin(value).count("1")


def parity(value: int) -> int:
    return popcount(value) & 1


def character_has_zero(p_value: int, y_value: int) -> bool:
    """Return whether the character indexed by (P,Y) has a zero on C."""
    if not 0 <= p_value < 64 or not 0 <= y_value < 64:
        raise ValueError("P and Y must be six-bit integers")

    if parity(p_value) == 1:
        return True

    p0 = p_value & 1
    p = (p_value >> 1) & 0b11111
    y = (y_value >> 1) & 0b11111
    r = p ^ (0b11111 if p0 else 0)

    return (
        popcount(r) == 2
        and parity(y_value) == 1
        and parity(r & y) == (1 ^ p0)
    )


def count_characters() -> tuple[int, int]:
    zero_free = 0
    has_zero = 0
    for p_value in range(64):
        for y_value in range(64):
            if character_has_zero(p_value, y_value):
                has_zero += 1
            else:
                zero_free += 1
    return zero_free, has_zero


if __name__ == "__main__":
    zero_free, has_zero = count_characters()
    print(f"zero-free: {zero_free}")
    print(f"has a zero: {has_zero}")
