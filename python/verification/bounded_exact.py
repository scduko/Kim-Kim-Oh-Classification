"""§4.2, Appendix A.3 and Table 4: the last-column test, U(B) and bounded integral lifts."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import cache, lru_cache
from itertools import product
from math import isqrt

from local_representation import determinant, represents
from residue_census import triadic_directions
from scalar_sieve import ranges, weighted_gap_bound
from notation import MAX_LOCAL_STEP, TARGET_HOSTS, least_step
from block_filter import block_profiles, classify_range, worst_steps
from terminal_corrections import certify_range, prime_factors_from_five



@cache
def directions(xmax,ymax):
    """Order the possible leading pairs up to sign, shortest sup norm first."""
    pairs = ((x,y) for x in range(xmax+1) for y in range(-ymax,ymax+1)
             if x or y >= 0)
    return tuple(sorted(pairs,key=lambda z:(max(map(abs,z)),z)))


def ceil_div(n,d):
    return -((-n)//d)


@cache
def completions(modulus, binary):
    rows = product(range(modulus), repeat=3)
    if modulus == 8:
        return tuple(last for last in rows if determinant(binary+last) % 4)
    return tuple(last for last in rows if any(binary+last))


def choices(target,binary,delta):
    host,scale = TARGET_HOSTS[target]
    a,b,c = binary
    for x,y in directions(isqrt((a-1)//scale),isqrt((c-1)//scale)):
        u,v = a-scale*x*x,c-scale*y*y
        Delta = delta-scale*(c*x*x-2*b*x*y+a*y*y)
        if u <= 0 or Delta <= 0:
            continue
        restrictions = []
        for p in prime_factors_from_five(Delta):
            if any(pow(host*z%p,(p-1)//2,p)==1 for z in (u,v)):
                continue
            if a%p == b%p == c%p == x%p == y%p == 0:
                break
            weight = 2 if delta % p == 0 and any(z % p for z in binary) else 1
            restrictions.append((p,weight))
        else:
            gap = weighted_gap_bound(tuple(restrictions))
            if gap is not None:
                yield x,y,scale*gap**2,Delta


@cache
def step_masks(modulus,target,binary,x,y):
    """Sets of last columns grouped by the least permissible step in k."""
    host,scale = TARGET_HOSTS[target]
    period = 3 if modulus==3 else (2 if target==6 else 4)
    a,b,c = binary
    leading = tuple(z%modulus for z in (a-scale*x*x,b-scale*x*y,c-scale*y*y))
    masks = {}
    coarse = tuple(v%modulus for v in binary)
    for i,(d,e,f) in enumerate(completions(modulus,coarse)):
        allowed = []
        for k in range(period):
            if modulus == 3:
                good = (x,y,k) in triadic_directions(host,binary)[d,e,f]
            else:
                corrected_gram = leading + ((d-scale*x*k)%8,(e-scale*y*k)%8,(f-scale*k*k)%8)
                good = represents(host,2,corrected_gram)
            if good:
                allowed.append(k)
        step = least_step(tuple(k in allowed for k in range(period)))
        if step:
            masks[step] = masks.get(step,0) | (1<<i)
    return tuple(masks.items())


@cache
def row_starts(rows,width):
    """Space the active row bits so multiplication inserts the same column mask in each row."""
    result = 0
    while rows:
        bit = rows & -rows
        result |= 1 << ((bit.bit_length()-1)*width)
        rows ^= bit
    return result


@lru_cache(maxsize=60000)
def cover(two,three,width,largest_step):
    result = 0
    for step,rows in two:
        columns = sum(bits for other,bits in three if step*other <= largest_step)
        if columns:
            result |= row_starts(rows,width)*columns
    return result


def local_choices(target,binary,delta,dyadic):
    period = 2 if target==6 else 4
    triadic = tuple(v%9 for v in binary)
    for x,y,scaled_gap_squared,Delta in choices(target,binary,delta):
        two = step_masks(8,target,dyadic,x%period,y%period)
        if two:
            three = step_masks(3,target,triadic,x%3,y%3)
            if three:
                yield two,three,scaled_gap_squared,Delta


def bounds(target,binary,delta,D0):
    dyadic,triadic = tuple(t%8 for t in binary),tuple(t%3 for t in binary)
    two_rows = completions(8,dyadic)
    three_rows = completions(3,triadic)
    width = len(three_rows)
    # One bit for each Cartesian pair of dyadic and triadic completions.
    remaining = (1 << (len(two_rows)*width))-1
    if not remaining:
        return None
    for two,three,scaled_gap_squared,Delta in local_choices(target,binary,delta,dyadic):
        largest_step = isqrt((4*Delta*D0-1)//(delta*delta*scaled_gap_squared))
        if largest_step:
            remaining &= ~cover(two,three,width,min(MAX_LOCAL_STEP,largest_step))
        if not remaining:
            return None
    # Recover the completion classes which can still occur at the reduction minimum.
    possible = {}
    bits = remaining
    while bits:
        bit = bits & -bits
        ii,jj = divmod(bit.bit_length()-1,width)
        # CRT: 9 is (1,0) and 16 is (0,1) modulo (8,3).
        d,e,f = ((9*u+16*v)%24 for u,v in zip(two_rows[ii],three_rows[jj]))
        possible.setdefault((d,e),[]).append(f)
        bits ^= bit

    # A single bound applies to every possible completion of this binary block.
    claims = []
    for two,three,scaled_gap_squared,Delta in local_choices(target,binary,delta,dyadic):
        for m2,rows in two:
            for m3,cols in three:
                mask = (row_starts(rows,width)*cols) & remaining
                if mask:
                    upper_det = delta*delta*scaled_gap_squared*(m2*m3)**2//(4*Delta)
                    claims.append((upper_det,mask))
    # First claim covering a class is its least bound. The last new class
    # covered therefore gives U(B), the maximum of these class minima.
    for upper_det,mask in sorted(claims):
        remaining &= ~mask
        if not remaining:
            return upper_det,possible
    raise ArithmeticError(("completion without a bound",target,binary))

def census(target,binary,delta,D0,upper_det,residues,counts):
    a,b,c = binary
    for d in range(a//2+1):
        first_e = ceil_div(2*b*d-delta,2*a)
        if d==0:
            first_e = max(0,first_e)
        if b==0 or 2*b==a:
            first_e = max(first_e,ceil_div(b*d,a))
        for e in range(first_e,(2*b*d+delta)//(2*a)+1):
            allowed = residues.get((d%24,e%24))
            if not allowed:
                continue
            block_form = c*d*d-2*b*d*e+a*e*e
            low = max(a,ceil_div(delta+d*d,a),ceil_div(D0+block_form,delta))
            for residue in allowed:
                start = low+(residue-low)%24
                top = (upper_det+block_form)//delta
                if start <= top:
                    counts['bounded'] += 1+(top-start)//24
                    certify_range(target,binary,d,e,start,top,counts)

ALL_BLOCK_FIELDS = ("binary","retained","bounded","tested")
FIELDS = ("binary","left_by_whole_block_test","retained","bounded","tested")
EXPECTED = {6:(534827,836,99,29831,10905), 9:(8521181,5147,162,10407,7556)}
ALL_BLOCK_EXPECTED = {6:(1835695,191,68853,23981),
            9:(23103909,162,10407,7556)}


def sweep_all_blocks(job):
    target, start, stop = job
    counts = Counter()
    intervals = ranges(TARGET_HOSTS[target][0])
    for a in range(start,stop):
        for _,low,high in intervals.get(a, ()):
            for b in range(a//2+1):
                for c in range(max(a,ceil_div(low+b*b,a)),(high+b*b)//a+1):
                    binary=(a,b,c)
                    if not completions(8,(a%8,b%8,c%8)):
                        continue
                    counts["binary"] += 1
                    delta=a*c-b*b
                    D0=ceil_div(3*delta*delta,4*a)
                    row_bounds=bounds(target,binary,delta,D0)
                    if row_bounds:
                        counts["retained"] += 1
                        census(target,binary,delta,D0,*row_bounds,counts)
    return target,counts


def sweep(job):
    target, start, stop = job
    host = TARGET_HOSTS[target][0]
    counts = Counter()
    intervals = ranges(host)
    for a in range(start, stop):
        for t, low, high in intervals.get(a, ()):
            for binary, delta in classify_range(host, a, t, low, high, counts):
                D0 = ceil_div(3*delta**2, 4*a)
                row_bounds = bounds(target, binary, delta, D0)
                if row_bounds:
                    counts["retained"] += 1
                    census(target,binary,delta,D0,*row_bounds,counts)
    return target,counts


def verify(workers, all_blocks=False):
    totals={6:Counter(),9:Counter()}
    stops={target:max(ranges(TARGET_HOSTS[target][0]))+1 for target in totals}
    fields, expected = (ALL_BLOCK_FIELDS, ALL_BLOCK_EXPECTED) if all_blocks else (FIELDS, EXPECTED)
    if not all_blocks:
        for host in (3,9):
            for prime in (2,3):
                block_profiles(host, prime)
                worst_steps(host, prime)
    jobs=[(target,a,min(a+6,stop)) for target,stop in stops.items() for a in range(2,stop,6)]
    with ProcessPoolExecutor(workers) as pool:
        for target,result in pool.map(sweep_all_blocks if all_blocks else sweep,jobs):
            totals[target].update(result)
    labels = {
        "binary": "Binary blocks in the region for H_j(B,t)",
        "left_by_whole_block_test": "Blocks with D bounded by last-column class",
        "retained": "Blocks with a last-column class of bound at least D0",
        "bounded": "Bounded integral lifts in those classes",
        "tested": "Ternary Gram matrices tested individually",
    }
    census_title = "Certificate 4.3, Table 4"
    if all_blocks:
        census_title = "Last-column bounds on all blocks in the uniform ranges"
        labels["binary"] = "Binary blocks considered in the uniform ranges"
    for target,counts in totals.items():
        actual=tuple(counts[name] for name in fields)
        print(f"L{target}: {census_title}", flush=True)
        for name in fields:
            print(f"  {labels[name]}: {counts[name]}", flush=True)
        radii = tuple(counts[r] for r in range(3))
        print(f"L{target} witnesses of sup norms 0 / 1 / 2 = {radii}.",flush=True)
        if actual != expected[target]:
            raise ArithmeticError(("unexpected enumeration counts", target, actual))



if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers",type=int,default=1)
    args=parser.parse_args()
    if args.workers<1:
        parser.error("workers must be positive")
    verify(args.workers)
