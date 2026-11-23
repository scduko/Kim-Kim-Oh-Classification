"""§4.1 and Appendix A.2: all-lifts sets 𝒰_{j,p}(σ) and progression-step profiles."""
from functools import cache
from itertools import product
from math import prod

from local_representation import acceptance_table, pack, residues, source_flags, translated, unpack

ENTRIES = ((0,0), (0,1), (1,1), (0,2), (1,2), (2,2))
from notation import SCALES


@cache
def excluded(host,p):
    """For each z modulo p mark the source residues with at least one failing lift."""
    space = residues(p)
    q,r = space.q,space.r
    moduli = (q,r,q,r,r,q)
    scale = SCALES[host]
    period = (2 if scale == 2 else 4) if p == 2 else 9
    unmarked = pack(bytes(1-x for x in acceptance_table(host,p)))
    excluded = {}
    for v in product(range(period),repeat=3):
        z = tuple(t % p for t in v)
        correction = tuple(scale*v[i]*v[j] for i,j in ENTRIES)
        # G - s vv^T is unmarked precisely when G belongs to this translate.
        excluded[z] = excluded.get(z,0) | translated(unmarked,moduli,correction)
    return excluded


@cache
def permissible(host,p):
    """One acceptance byte per Gram residue for each covector modulo p."""
    size = residues(p).size
    full = (1 << size)-1
    return {z: unpack(full ^ bits,size) for z,bits in excluded(host,p).items()}


@cache
def triadic_directions(host,binary):
    """Allowed covectors modulo three, with the leading Gram block fixed modulo nine."""
    space = residues(3)
    start = space.encode(*binary,0,0,0)
    width = prod(space.moduli[3:])
    maximal = pack(source_flags(3)[start:start+width])
    lift_zero = sum(1 << space.encode(0,0,0,*row) for row in product((0,3,6),repeat=3))
    bad = {z: ((bits >> start) & maximal) for z,bits in excluded(host,3).items()}
    allowed = {}
    for row in product(range(3),repeat=3):
        lifts = lift_zero << space.encode(0,0,0,*row)
        allowed[row] = frozenset(z for z,bits in bad.items() if not bits & lifts)
    return allowed


@cache
def steps(p, flags):
    """Permissible steps for y, k, with k's starting residue depending on y."""
    sizes = [sum(flags[p*y:p*(y+1)]) for y in range(p)]
    if min(sizes) == p:
        return ((1, 1),)
    options = []
    if min(sizes) > 0:
        options.append((1, p))
    if max(sizes) == p:
        options.append((p, 1))
    if not options and max(sizes):
        options.append((p, p))
    return tuple(options)


@cache
def profile(p, flags):
    return tuple(steps(p, flags[x*p*p:(x+1)*p*p]) for x in range(p))


def maximal_profiles(host, p):
    """Yield the Gram residue index and its progression steps for each maximal class."""
    accepted = permissible(host, p)
    columns = [accepted[z] for z in product(range(p), repeat=3)]
    for code, row in enumerate(zip(source_flags(p), *columns)):
        if row[0]:
            yield code, profile(p, row[1:])


@cache
def local_profiles(host, p):
    """Step choices at each x, grouped by the first Gram entry."""
    space = residues(p)
    modulus = 4 if p == 2 else 3
    profiles = [set() for _ in range(modulus)]
    stride = space.size // space.q
    for code, options in maximal_profiles(host, p):
        profiles[(code//stride) % modulus].add(options)
    return profiles
