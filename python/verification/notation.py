"""Parameters shared by the search and the certificate file formats."""
from functools import cache
from math import gcd

# L_target = K_host ⊥ <scale>, with host = j and scale = s.
TARGET_HOSTS = {6: (3, 2), 9: (9, 1)}
SCALES = {host: scale for host, scale in TARGET_HOSTS.values()}
FIRST_ENTRIES = (0, 1, 2, 3, 6)
MAX_SX_SQUARED = max(SCALES.values()) * max(FIRST_ENTRIES)**2
PERIODIC_START = MAX_SX_SQUARED + 1
SIGNED_DIVISOR_WIDTH = 2 * 6  # x = 0 gives |y| ≤ 6.
MAX_LOCAL_STEP = 4 * 3         # Steps for k at 2 and 3 divide 4 and 3.
TAIL_COEFFICIENT = 2 * PERIODIC_START * (36 // 4 + 36 // 3)  # 3066 in A.2.

# Each direction has 0 ≤ x ≤ 6 and −6 ≤ y ≤ 6. Its byte is at most 90.
DEFER = 255


def encode_direction(x, y):
    if not (0 <= x <= 6 and -6 <= y <= 6 and (x or y > 0)
            and gcd(x, y) in (1, 2, 3, 4, 6)):
        raise ValueError(("invalid block direction", x, y))
    return 13*x + y + 6


def decode_direction(code):
    x, offset = divmod(code, 13)
    y = offset - 6
    encode_direction(x, y)  # Also rejects the reserved byte and noncanonical signs.
    return x, y


@cache
def least_step(flags):
    """Least step of a full congruence class in this period, or zero if empty."""
    period = len(flags)
    for step in range(1, period + 1):
        if period % step == 0 and any(all(flags[i::step]) for i in range(step)):
            return step
    return 0
