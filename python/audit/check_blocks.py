"""Certificate 4.3(a): reconstruct the region for H_j(B,t) and check the whole-block test."""
import base64
from fractions import Fraction
from functools import cache, lru_cache
import gzip
from itertools import product
import json
from math import gcd, isqrt, prod

from verify_steps_and_ranges import (FIRST_ENTRIES, SCALES, allowed_directions,
                            uniform_gap_bounds, profile, shift_axis, signed_divisor_works)

from verification.notation import DEFER, MAX_SX_SQUARED, SIGNED_DIVISOR_WIDTH, decode_direction
PERIODS = {2: 4, 3: 3}


def read_block_records(path):
    groups = {}
    for target, a, t, data in json.loads(gzip.decompress(path.read_bytes())):
        key = target, a, t
        if key in groups:
            raise ValueError(("duplicate block group", key))
        groups[key] = base64.b64decode(data, validate=True)
    return groups


@cache
def steps_for_row(period, flags):
    """One least step for each fixed x,y in this one completed Gram residue."""
    result = []
    for start in range(0, len(flags), period):
        row = flags[start:start+period]
        if all(row):
            result.append(1)
        elif period == 4 and ((row[0] and row[2]) or (row[1] and row[3])):
            result.append(2)
        elif any(row):
            result.append(period)
        else:
            result.append(0)
    return tuple(result)


@cache
def checked_tables(host, prime):
    """Group the profiles and permissible k steps by leading Gram residue.

    A common step must work for every maximal completion of the block.
    Its starting residue may depend on the completion. Zero means at
    least one completion admits no arithmetic progression for this direction.
    """
    from local_representation import acceptance_table, residues, source_flags
    moduli = residues(prime).moduli
    accepted = acceptance_table(host, prime)
    scale = SCALES[host]
    universal = allowed_directions(accepted, prime, scale, moduli)
    # The profiles use all lifts at both primes. For the whole-block
    # test, fixing x, y, k modulo 4 determines the correction at 2.
    if prime == 2:
        fixed = []
        for x, y, k in product(range(4), repeat=3):
            offsets = (x*x,x*y,y*y,x*k,y*k,k*k)
            flags = accepted
            stride = len(flags)
            for radix, entry in zip(moduli, offsets):
                stride //= radix
                flags = shift_axis(flags, radix, stride, scale*entry % radix)
            fixed.append(flags)
    else:
        fixed = universal
    period = PERIODS[prime]
    width = prod(moduli[3:])
    maximal = source_flags(prime)
    groups = {}
    by_prefix = []
    worst = []
    for start in range(0, len(accepted), width):
        stop = start + width
        maximal_flags = maximal[start:stop]
        profile_rows = zip(maximal_flags, *(flags[start:stop] for flags in universal))
        profiles = frozenset(profile(prime, row[1:]) for row in profile_rows if row[0])
        by_prefix.append(groups.setdefault(profiles, len(groups)))

        direction_rows = zip(maximal_flags, *(flags[start:stop] for flags in fixed))
        steps_by_completion = {steps_for_row(period, row[1:])
                               for row in direction_rows if row[0]}
        # Transpose so each column holds the steps for one direction over
        # all maximal completions. The local steps form a divisibility chain.
        worst.append(tuple(0 if 0 in steps else max(steps)
                           for steps in zip(*steps_by_completion)))
    return tuple(by_prefix), tuple(groups), tuple(worst)


@cache
def checked_pair_bound(host, a, g, pair2, pair3):
    s = SCALES[host]
    costs = []
    for x in FIRST_ENTRIES:
        if s*x*x >= a:
            continue
        for (h2,m2),(h3,m3) in product(pair2[x%2], pair3[x%3]):
            h, m = h2*h3, m2*m3
            if x == 0 and (a>MAX_SX_SQUARED or not signed_divisor_works(host, a, h)):
                continue
            w = h*g if x else SIGNED_DIVISOR_WIDTH
            costs.append(Fraction(s*a, a-s*x*x)*(Fraction(w*w,4)+Fraction((m*g)**2,3)))
    if not costs:
        raise ValueError(("no choices in a local case", host, a))
    return min(costs)


@cache
def checked_block_delta_bound(host, a, t, index2, index3):
    left, right = checked_tables(host,2)[1][index2], checked_tables(host,3)[1][index3]
    if not left or not right:
        return -1
    g = checked_gap_bounds()[t]
    return int(a*max(checked_pair_bound(host,a,g,u,v) for u,v in product(left,right)))


checked_gap_bounds = cache(uniform_gap_bounds)


@lru_cache(maxsize=150000)
def prime_factors_from_five(n):
    factors = []
    for p in (2,3):
        while n % p == 0:
            n //= p
    d = 5
    while d*d <= n:
        if n%d == 0:
            factors.append(d)
            while n%d == 0:
                n //= d
        d += 2
    if n > 1:
        factors.append(n)
    return tuple(factors)


def floor_log53(n):
    power, r = 53, 0
    while power <= n:
        r += 1
        power *= 53
    return r


def certifies(host, B, delta, x, y, m, check_factors=False):
    a,b,c = B
    s = SCALES[host]
    Delta = (a-s*x*x)*(c-s*y*y) - (b-s*x*y)**2
    if Delta <= 0:
        return False
    # Largest g satisfying the strict inequality s*a*(m*g)^2 < 3*Delta.
    limit = isqrt((3*Delta-1)//(s*a*m*m))
    if not limit:
        return False
    factors = prime_factors_from_five(Delta)
    small = tuple(p for p in factors if p < 53)
    small_product = prod(small)
    # Each distinct remaining prime contributes a factor of at least 53.
    # Only primes shared with delta can contribute a second forbidden class.
    r = floor_log53(Delta//small_product)
    r2 = floor_log53(gcd(delta,Delta))
    weights = tuple(1 + int(delta%p==0 and any(v%p for v in B)) for p in small)
    for g in range(1+sum(weights)+r+r2, limit+1):
        loss = sum(w*((g+p-1)//p) for p,w in zip(small,weights)) + (r+r2)*((g+52)//53)
        if loss < g:
            if check_factors:
                exact_loss = sum((1+int(delta%p==0 and any(v%p for v in B)))*((g+p-1)//p)
                                 for p in factors)
                if exact_loss > loss or exact_loss >= g or s*a*(m*g)**2 >= 3*Delta:
                    raise ValueError(("invalid block witness",B,x,y,m,g))
            return True
    return False


@cache
def alternatives(two, three):
    choices = []
    for x in range(7):
        for y in range(-6,7):
            if (x == 0 and y <= 0) or gcd(x,y) not in (1,2,3,4,6):
                continue
            m2, m3 = two[4*(x%4)+y%4], three[3*(x%3)+y%3]
            if m2 and m3:
                choices.append((x,y,m2*m3))
    return choices


def deferred_blocks(host, a, t, lo, hi, record, counts):
    groups2, _, steps2 = checked_tables(host,2)
    groups3, _, steps3 = checked_tables(host,3)
    # The file has one byte per block in the region, in this (b,c) order.
    # Check each direction or reconstruct the alternatives for a deferred block.
    at = 0
    for b in range(a//2+1):
        for c in range(max(a,(lo+b*b+a-1)//a),(hi+b*b)//a+1):
            B = a,b,c
            delta = a*c-b*b
            i2 = ((a%8)*4+b%4)*8+c%8
            i3 = ((a%9)*9+b%9)*9+c%9
            if delta > checked_block_delta_bound(host,a,t,groups2[i2],groups3[i3]):
                continue
            if at == len(record):
                raise ValueError(("missing block direction",host,B,t))
            code = record[at]
            at += 1
            counts["in_region"] += 1
            counts["in_region",t] += 1
            two,three = steps2[i2],steps3[i3]
            if code == DEFER:
                if any(certifies(host,B,delta,x,y,m) for x,y,m in alternatives(two,three)):
                    raise ValueError(("deferred block passed the whole-block test",host,B))
                counts["deferred"] += 1
                counts["deferred",t] += 1
                yield B,delta
            else:
                x,y = decode_direction(code)
                m2,m3 = two[4*(x%4)+y%4],three[3*(x%3)+y%3]
                if not m2 or not m3 or not certifies(host,B,delta,x,y,m2*m3,True):
                    raise ValueError(("unproved block removal",host,B,x,y))
    if at != len(record):
        raise ValueError(("extra block directions",host,a,t))
