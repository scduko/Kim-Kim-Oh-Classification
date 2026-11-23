"""§4.1 and A.2: g_t, H_j(a,t), the tail t ≥ 27 and Certificates 4.1–4.2."""
from fractions import Fraction
from functools import cache
from itertools import accumulate, product
from math import isqrt, prod
from operator import mul

from notation import FIRST_ENTRIES, PERIODIC_START, SCALES, SIGNED_DIVISOR_WIDTH, TAIL_COEFFICIENT
from residue_census import local_profiles

PRIMES = tuple(p for p in range(5, 320) if all(p % d for d in range(2, isqrt(p) + 1)))
PRODUCTS = (1,) + tuple(accumulate(PRIMES, mul))
TAIL = 27

@cache
def choices(host, a):
    cases = set()
    for two, three in product(local_profiles(host, 2)[a % 4], local_profiles(host, 3)[a % 3]):
        options = set()
        for x in FIRST_ENTRIES:
            if x or a < PERIODIC_START:
                # The local moduli are coprime. The common differences for
                # y and k over the integers are the products of their local steps.
                for (h2, m2), (h3, m3) in product(two[x % 2], three[x % 3]):
                    options.add((x, h2 * h3, m2 * m3))
        cases.add(frozenset(options))
    return cases


@cache
def weighted_gap_bound(restrictions):
    """A length guaranteeing a survivor with at most w forbidden classes at each prime."""
    if not restrictions:
        return 1
    n = 1 + sum(w for p,w in restrictions)
    if n <= min(p for p,w in restrictions):
        return n
    if sum(Fraction(w,p) for p,w in restrictions) >= 1:
        return None
    while True:
        loss = sum(w*((n+p-1)//p) for p,w in restrictions)
        if loss < n:
            return n
        n = loss+1


@cache
def uniform_gap_bound(t):
    return weighted_gap_bound(tuple((p,1) for p in PRIMES[:t]))


def check_tail():
    if sum(Fraction(1,p) for p in PRIMES[:TAIL-1]) >= 1:
        raise ArithmeticError("finite gap bounds require sum(1/p) < 1")
    bound = (TAIL+4)*2**(TAIL-2)
    # The next prime must give √q_(t+1) > 4 ((t+5)/(t+4))² at t = 27.
    if (3*PRODUCTS[TAIL] <= 4*(TAIL_COEFFICIENT*bound**2)**2 or
            PRIMES[TAIL]*(TAIL+4)**4 <= 16*(TAIL+5)**4):
        raise ArithmeticError("gap estimate for t >= 27")


@cache
def admits_signed_divisor(host, scale, a, step):
    """When x is zero, choose the second coefficient among the signed divisors of six."""
    primes = [p for p in PRIMES if a % p == 0]
    signed = (1, -1, 2, -2, 3, -3, 6, -6)
    for c in range(prod(primes)):
        for start in range(step):
            if not any(y % step == start and
                       all(c % p == 0 or pow(host*(c - scale*y*y), (p-1)//2, p) != p-1
                           for p in primes) for y in signed):
                return False
    return True


@cache
def uniform_beta_bound(host, a, t):
    """A failing block has beta at most this exact rational number."""
    scale = SCALES[host]
    group = a if a < PERIODIC_START else PERIODIC_START + (a-PERIODIC_START) % 12

    @cache
    def scalar_cost(option):
        x, h, m = option
        if scale*x*x >= a:
            return None
        if not x and not admits_signed_divisor(host, scale, a, h):
            return None
        gap = uniform_gap_bound(t)
        width = h * gap if x else SIGNED_DIVISOR_WIDTH
        return Fraction(scale * a, a - scale * x*x) * (
            Fraction(width**2, 4) + Fraction((m * gap)**2, 3)
        )

    bounds = []
    for case in choices(host,group):
        valid = [value for option in case if (value := scalar_cost(option)) is not None]
        if not valid:
            raise ArithmeticError(("no permissible triple (x,h,m)", host, a, case))
        bounds.append(min(valid))
    return max(bounds)


@cache
def ranges(host):
    """For each a, retain (t, low, high) for each inclusive interval of possible integer delta."""
    remaining = {}

    def insert(a,t):
        beta_bound = uniform_beta_bound(host,a,t)
        high = min(PRODUCTS[t+1]-1, int(a*beta_bound))
        low = max(PRODUCTS[t], (3*a*a + 3)//4)
        if low <= high:
            remaining.setdefault(a,[]).append((t,low,high))

    for t in range(TAIL):
        for a0 in range(2,PERIODIC_START+12):
            beta_bound=uniform_beta_bound(host,a0,t)
            if a0<PERIODIC_START:
                insert(a0,t)
            elif 3*PRODUCTS[t] <= 4*beta_bound**2:
                for a in range(a0, int(4*beta_bound/3)+1,12):
                    insert(a,t)
    return remaining


def main():
    check_tail()
    for host in (3,9):
        spans=ranges(host)
        max_a=max(spans)
        max_beta=max(Fraction(hi,a) for a, intervals in spans.items() for _,_,hi in intervals)
        print(f"K{host}: remaining binary ranges have a <= {max_a}, beta <= {max_beta}.",flush=True)


if __name__ == "__main__":
    main()
