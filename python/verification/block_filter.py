"""§4.2 and A.3: H_j(B,t), the local steps m_p, the whole-block test (8) and Lemma A.1."""
from functools import cache, lru_cache
from itertools import product
from math import gcd, isqrt, prod

from local_representation import acceptance_table, pack, residues, source_flags, translated, unpack
from notation import DEFER, FIRST_ENTRIES, MAX_SX_SQUARED, SCALES, SIGNED_DIVISOR_WIDTH, encode_direction, least_step
from residue_census import ENTRIES, maximal_profiles, permissible
from scalar_sieve import admits_signed_divisor, uniform_gap_bound

SMALL_PRIMES = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
SMALL_PRODUCT = prod(SMALL_PRIMES)
DIRECTIONS = tuple(sorted(
    ((x, y) for x in range(7) for y in range(-6, 7)
     if (x or y > 0) and gcd(x, y) in (1, 2, 3, 4, 6)),
    key=lambda pair: (max(map(abs, pair)), pair)))


@cache
def block_profiles(host, p):
    space = residues(p)
    width = prod(space.moduli[3:])
    groups = [set() for _ in range(space.size // width)]
    for code, options in maximal_profiles(host, p):
        groups[code // width].add(options)
    return intern(tuple(frozenset(group) for group in groups))


def intern(groups):
    """Index repeated local data, keeping one copy for each distinct value."""
    values = tuple(dict.fromkeys(groups))
    indices = {value: i for i, value in enumerate(values)}
    return tuple(indices[g] for g in groups), values


@cache
def local_triples(two, three):
    return tuple((x, h2*h3, m2*m3)
                 for x in FIRST_ENTRIES
                 for h2, m2 in two[x%2] for h3, m3 in three[x%3])


@cache
def block_delta_bound(host, a, t, id2, id3):
    """Integer part of a H_j(B,t); -1 means no maximal completion at a prime."""
    g = uniform_gap_bound(t)
    left = block_profiles(host, 2)[1][id2]
    right = block_profiles(host, 3)[1][id3]
    if not left or not right:
        return -1
    return max(case_delta_bound(host, a, g, two, three) for two, three in product(left, right))


@cache
def case_delta_bound(host, a, g, two, three):
    s = SCALES[host]
    costs = []
    for x, h, m in local_triples(two, three):
        if s*x*x >= a or (not x and (a > MAX_SX_SQUARED or not admits_signed_divisor(host, s, a, h))):
            continue
        w = h*g if x else SIGNED_DIVISOR_WIDTH
        costs.append(s*a*a*(3*w*w + 4*(m*g)**2) // (12*(a-s*x*x)))
    if not costs:
        raise ValueError(("no valid triple", host, a, two, three))
    return min(costs)


@cache
def worst_steps(host, p):
    """For each leading residue and direction, the common step with starting class depending on the completion G."""
    space = residues(p)
    width = prod(space.moduli[3:])
    prefixes = space.size // width
    period = 4 if p == 2 else 3
    if p == 2:
        table = pack(acceptance_table(host, p))
        def flags(x, y, k):
            v = x,y,k
            shift = tuple(SCALES[host]*v[i]*v[j] for i,j in ENTRIES)
            return unpack(translated(table, space.moduli, shift), space.size)
    else:
        directions = permissible(host, 3)
        def flags(x, y, k):
            return directions[x,y,k]
    maximal = source_flags(p)
    result = [[] for _ in range(prefixes)]
    for x, y in product(range(period), repeat=2):
        columns = [flags(x, y, k) for k in range(period)]
        by_prefix = [1]*prefixes
        for code, row in enumerate(zip(maximal, *columns)):
            if row[0]:
                step = least_step(row[1:])
                index = code//width
                if step == 0 or by_prefix[index] == 0:
                    by_prefix[index] = 0
                else:
                    by_prefix[index] = max(by_prefix[index], step)
        for row, step in zip(result, by_prefix):
            row.append(step)
    return intern(tuple(tuple(row) for row in result))


@cache
def allowed_directions(host, id2, id3):
    two, three = worst_steps(host, 2)[1][id2], worst_steps(host, 3)[1][id3]
    out = []
    for x,y in DIRECTIONS:
        m = two[4*(x%4) + y%4] * three[3*(x%3) + y%3]
        if m:
            out.append((x,y,m))
    return tuple(out)


def log53(n):
    r = 0
    while n >= 53:
        r += 1
        n //= 53
    return r


@lru_cache(maxsize=100000)
def small_factors(n):
    return tuple(p for p in SMALL_PRIMES if n % p == 0)


def has_window(delta, Delta, block_gcd, limit):
    """Lemma A.1: does the bound for the larger primes certify a g ≤ limit?"""
    # 35 = 5·7. Below it there is at most one small prime; shared < 5
    # makes all weights one. For g ≤ 5 every ceiling is one.
    small = gcd(Delta, SMALL_PRODUCT)
    shared = gcd(Delta, delta)
    r = log53(Delta // small)
    if small < 35 and shared < 5:
        g = 1 + int(small > 1) + r
        if g <= 5:
            return g <= limit
    # The larger primes contribute at most (r+r2) ceil(g/53).
    r2 = log53(shared)
    primes = small_factors(small)
    weights = tuple(2 if shared % p == 0 and block_gcd % p else 1 for p in primes)
    g = 1 + sum(weights) + r + r2
    while g <= limit:
        loss = (r+r2)*((g+52)//53) + sum(w*((g+p-1)//p) for p,w in zip(primes,weights))
        if loss < g:
            return True
        g = loss+1
    return False


def certifying_direction(host, a, b, c, delta, possible):
    s = SCALES[host]
    block_gcd = gcd(a,b,c)
    for x,y,m in possible:
        Delta = delta-s*(c*x*x-2*b*x*y+a*y*y)
        if Delta <= 0:
            continue
        limit = isqrt((3*Delta-1)//(s*a*m*m))
        if limit and has_window(delta, Delta, block_gcd, limit):
            return x, y
    return None


def classify_range(host, a, t, low, high, counts, records=None):
    """Yield the blocks in the region for H_j(B,t) passed to the last-column test."""
    p2, p3 = block_profiles(host,2)[0], block_profiles(host,3)[0]
    d2, d3 = worst_steps(host,2)[0], worst_steps(host,3)[0]
    space2, space3 = residues(2), residues(3)
    width2, width3 = prod(space2.moduli[3:]), prod(space3.moduli[3:])
    for b in range(a//2+1):
        base2 = space2.encode(a%8, b%4, 0, 0, 0, 0) // width2
        base3 = space3.encode(a%9, b%9, 0, 0, 0, 0) // width3
        for c in range(max(a,(low+b*b+a-1)//a),(high+b*b)//a+1):
            delta = a*c-b*b
            i2, i3 = base2+c%8, base3+c%9
            if delta > block_delta_bound(host,a,t,p2[i2],p3[i3]):
                continue
            counts['binary'] += 1
            possible = allowed_directions(host,d2[i2],d3[i3])
            direction = certifying_direction(host,a,b,c,delta,possible)
            if records is not None:
                code = DEFER if direction is None else encode_direction(*direction)
                records.append(code)
            if direction is None:
                counts['left_by_whole_block_test'] += 1
                yield (a,b,c), delta
