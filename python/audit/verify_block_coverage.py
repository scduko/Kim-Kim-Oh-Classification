"""Certificate 4.3(b,c): check last-column classes, U(B), the bounded enumeration and the list of matrices."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import cache, lru_cache
import gzip
from itertools import product
import json
from math import isqrt, prod
from pathlib import Path
import sys

from check_blocks import checked_tables, deferred_blocks, prime_factors_from_five, read_block_records
from verification.notation import MAX_LOCAL_STEP, TARGET_HOSTS
from coverage_sources import ceil_div, maximal_at_three, source_rows

from certificate_files import BLOCK_PAIRS, LAST_COLUMN_BOUNDS, GRAM_MATRICES

HERE = Path(__file__).resolve().parent
TWO = tuple(product(range(4),range(4),range(8)))
THREE = tuple(product(range(3),repeat=3))
WIDTH = len(TWO)


@cache
def dyadic_domain(binary):
    a,b,c = binary
    return sum(1<<i for i,(d,e,f) in enumerate(TWO)
               if ((a*c-b*b)*f-c*d*d+2*b*d*e-a*e*e)%4)


@cache
def three_lifts(binary):
    """All locally maximal modulo-nine lifts of each last column modulo three."""
    from local_representation import residues
    space = residues(3)
    lifts = []
    for d,e,f in THREE:
        codes = []
        for dd,ee,ff in THREE:
            gram = binary + (d+3*dd,e+3*ee,f+3*ff)
            if maximal_at_three(gram):
                codes.append(space.encode(*gram))
        lifts.append(tuple(codes))
    return tuple(lifts)


@cache
def three_domains(binary):
    coarse = sum(1<<i for i,row in enumerate(THREE) if any(v%3 for v in binary+row))
    maximal = sum(1<<i for i,codes in enumerate(three_lifts(binary)) if codes)
    return coarse,maximal


@cache
def progression(period, allowed):
    """Return the least possible full progression step, with zero for failure."""
    for m in range(1,period+1):
        if period%m==0:
            for start in range(m):
                if all((allowed>>k)&1 for k in range(start,period,m)):
                    return m
    return 0


@cache
def two_steps(target,binary,x,y):
    from local_representation import represents
    host,s = TARGET_HOSTS[target]
    a,b,c = binary
    period = 2 if s==2 else 4
    leading = a-s*x*x,b-s*x*y,c-s*y*y
    masks = {}
    for i,(d,e,f) in enumerate(TWO):
        allowed = sum(1<<k for k in range(period)
                      if represents(host,2,leading+(d-s*x*k,e-s*y*k,f-s*k*k)))
        m = progression(period,allowed)
        if m:
            masks[m] = masks.get(m,0) | (1<<i)
    return tuple(masks.items())


@cache
def three_steps(host,binary,x,y):
    from residue_census import permissible
    lookup = permissible(host,3)
    accepts = [lookup[x,y,k] for k in range(3)]
    masks = {}
    for i,codes in enumerate(three_lifts(binary)):
        # One k modulo 3 must work for every maximal Gram lift modulo 9.
        # A class with no such lift contains no maximal source.
        allowed = sum(1 << k for k, flags in enumerate(accepts)
                      if all(flags[code] for code in codes))
        m = progression(3,allowed)
        if m:
            masks[m] = masks.get(m,0) | (1<<i)
    return tuple(masks.items())


@cache
def expand_three(bits):
    return sum(1<<(i*WIDTH) for i in range(len(THREE)) if (bits>>i)&1)


@lru_cache(maxsize=60000)
def product_mask(two,three,step_limit):
    """One bit for every (three-adic row, two-adic row), in that order."""
    result=0
    for m,dyadic in two:
        for n,triadic in three:
            if m*n<=step_limit:
                result |= dyadic*expand_three(triadic)
    return result


@cache
def weighted_gap_bound(restrictions):
    denominator=prod(p for p,w in restrictions)
    if sum(w*(denominator//p) for p,w in restrictions)>=denominator:
        return 0
    g=1+sum(w for p,w in restrictions)
    while sum(w*ceil_div(g,p) for p,w in restrictions)>=g:
        g+=1
    return g


# These names are imported by the formalization's gen_terminal.py.
TARGETS = TARGET_HOSTS
primes_from_five = prime_factors_from_five
union_window = weighted_gap_bound


@cache
def leading_pairs(max_x,max_y):
    pairs=((x,y) for x in range(max_x+1) for y in range(-max_y,max_y+1) if x or y>=0)
    return sorted(pairs,key=lambda v:(max(map(abs,v)),v))


def options(target,binary,delta,b2,b3):
    host,s=TARGET_HOSTS[target]
    a,b,c=binary
    period = 2 if s==2 else 4
    for x,y in leading_pairs(isqrt((a-1)//s),isqrt((c-1)//s)):
        aa,bb,cc=a-s*x*x,b-s*x*y,c-s*y*y
        Delta=aa*cc-bb*bb
        if Delta<=0:
            continue
        restrictions=[]
        for p in prime_factors_from_five(Delta):
            if any(pow(host*u%p,(p-1)//2,p)==1 for u in (aa,cc)):
                continue
            zero_block=not (a%p or b%p or c%p)
            if zero_block and x%p==y%p==0:
                break
            weight=1 if delta%p or zero_block else 2
            restrictions.append((p,weight))
        else:
            g=weighted_gap_bound(tuple(restrictions))
            if g:
                two=two_steps(target,b2,x%period,y%period)
                three=three_steps(host,b3,x%3,y%3)
                if two and three:
                    yield two,three,4*Delta,s*g*g


def below_mask(options_for_pair, delta_squared, threshold):
    """An integer determinant bound is below threshold iff s*delta^2*g^2*m^2 < 4*Delta*threshold."""
    two,three,denom,scaled_gap_squared=options_for_pair
    limit=isqrt((denom*threshold-1)//(delta_squared*scaled_gap_squared))
    return product_mask(two,three,min(limit,MAX_LOCAL_STEP)) if limit else 0


def reader_bits(serialized):
    """Map stored bit ((r1 % 12)*12 + r2 % 12)*24 + f % 24 to
    128*pos3 + pos2. The lexicographic digits of pos3 have moduli
    (3,3,3), and those of pos2 have moduli (4,4,8).
    """
    result=0
    while serialized:
        bit=serialized & -serialized
        q,f=divmod(bit.bit_length()-1,24)
        d,e=divmod(q,12)
        pos3=((d%3)*3+e%3)*3+f%3
        pos2=((d%4)*4+e%4)*8+f%8
        result|=1<<(WIDTH*pos3+pos2)
        serialized ^=bit
    return result


def check_block(target,binary,delta,b2,b3,domain,record):
    """A missing record asserts that all class bounds lie below D0."""
    a,b,c=binary
    D0=ceil_div(3*delta**2,4*a)
    square=delta**2
    pending=domain
    if record:
        upper_det,serialized=record
        surviving=reader_bits(serialized)
        if not surviving or surviving&~domain or upper_det<D0:
            raise ValueError(("invalid survivor bitmap or determinant bound",target,binary))
        # Each option removes classes whose determinant bound is below the
        # threshold. After all options, the remaining classes have their
        # least bound at or above it. To verify U(B), all least bounds
        # must be at most upper_det and at least one must attain it.
        above_upper_bound = at_or_above_upper_bound = surviving
        for option in options(target, binary, delta, b2, b3):
            pending &= ~below_mask(option, square, D0)
            above_upper_bound &= ~below_mask(option, square, upper_det + 1)
            at_or_above_upper_bound &= ~below_mask(option, square, upper_det)
        if pending != surviving or above_upper_bound or not at_or_above_upper_bound:
            raise ValueError(("last-column class or determinant bound mismatch",target,binary,upper_det))
        return
    for option in options(target,binary,delta,b2,b3):
        pending &= ~below_mask(option,square,D0)
        if not pending:
            return
    if pending:
        raise ValueError(("unbounded or missing binary block",target,binary))


def read_records(path):
    """Read a hex bitmap on (r1 mod 12, r2 mod 12, f mod 24) for each block."""
    rows=json.loads(gzip.decompress(path.read_bytes()))
    mapping={}
    for target,a,b,c,upper_det,bitmap in rows:
        key=target,a,b,c
        bits=int(bitmap,16)
        if key in mapping or target not in TARGET_HOSTS or not 0<bits<1<<(24*12**2):
            raise ValueError(("invalid certificate row",key))
        mapping[key]=upper_det,bits
    return mapping


def sweep(job):
    target,items,records,block_records=job
    host = TARGET_HOSTS[target][0]
    counts=Counter()
    seen=set()
    sources=[]
    for a,intervals in items:
        for t,lo,hi in intervals:
            group = block_records.pop((target,a,t))
            for (a,b,c), delta in deferred_blocks(host,a,t,lo,hi,group,counts):
                b2=(a%8,b%4,c%8)
                mask2=dyadic_domain(b2)
                if not mask2:
                    raise ValueError(("no dyadic completion", target, a,b,c))
                b3=(a%9,b%9,c%9)
                coarse3,compatible3=three_domains(b3)
                domain=mask2*expand_three(coarse3)
                # Four nominal (d,e,f) mod 24 classes have one CRT bitmap bit.
                coarse=4*mask2.bit_count()*coarse3.bit_count()
                compatible=4*mask2.bit_count()*compatible3.bit_count()
                counts["coarse_residues"]+=coarse
                counts["incompatible_at_three"]+=coarse-compatible
                key=target,a,b,c
                record=records.get(key)
                check_block(target,(a,b,c),a*c-b*b,b2,b3,domain,record)
                if record:
                    seen.add(key)
                    upper_det,serialized=record
                    bitmap=reader_bits(serialized)
                    if bitmap & ~(mask2*expand_three(compatible3)):
                        raise ValueError(("surviving class with no maximal source", key))
                    counts["retained_blocks"]+=1
                    counts["surviving_coarse_residues"]+=4*bitmap.bit_count()
                    counts["surviving_compatible_residues"]+=4*(bitmap & (mask2*expand_three(compatible3))).bit_count()
                    for row,passes in source_rows(target,a,b,c,upper_det,serialized):
                        counts["bounded_lifts"]+=1
                        if passes:
                            sources.append(row)
    if block_records:
        raise ValueError("unvisited whole-block certificate group")
    if seen!=set(records):
        raise ValueError(("unvisited stored block",sorted(set(records)-seen)))
    return target,counts,sources


def encoded_sources(rows):
    if len(rows)!=len(set(rows)):
        raise ValueError("duplicate terminal source")
    return "".join(" ".join(map(str,row))+"\n" for row in sorted(rows)).encode("ascii")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers",type=int,default=1)
    parser.add_argument("--verification",type=Path,default=HERE.parent/"verification")
    parser.add_argument("--record",type=Path,default=LAST_COLUMN_BOUNDS)
    parser.add_argument("--sources",type=Path,default=GRAM_MATRICES)
    parser.add_argument("--blocks",type=Path,default=BLOCK_PAIRS)
    args=parser.parse_args()
    sys.path.insert(0,str(args.verification.resolve()))
    from scalar_sieve import ranges
    from residue_census import permissible
    records=read_records(args.record)
    block_records = read_block_records(args.blocks)
    jobs=[]
    for target,(host,s) in TARGET_HOSTS.items():
        for p in (2,3):
            checked_tables(host,p)
        intervals=ranges(host)
        permissible(host,3)
        rows=sorted(intervals.items())
        for start in range(0,len(rows),6):
            selection=rows[start:start+6]
            first_norms={a for a,interval in selection}
            subset={key:val for key,val in records.items() if key[0]==target and key[1] in first_norms}
            groups = {key:block_records.pop(key) for key in list(block_records)
                      if key[0]==target and key[1] in first_norms}
            jobs.append((target,selection,subset,groups))
    if block_records:
        raise ValueError("whole-block certificate outside uniform ranges")
    if sum(len(subset) for _,_,subset,_ in jobs)!=len(records):
        raise ValueError("stored first norm outside proof ranges")
    totals={target:Counter() for target in TARGET_HOSTS}
    sources=[]
    with ProcessPoolExecutor(args.workers) as pool:
        for target,counts,rows in pool.map(sweep,jobs):
            totals[target].update(counts)
            sources.extend(rows)
    if encoded_sources(sources)!=gzip.decompress(args.sources.read_bytes()):
        raise ValueError("terminal source list differs")
    for target,c in totals.items():
        compatible=c["coarse_residues"]-c["incompatible_at_three"]
        high=c["surviving_compatible_residues"]
        print(f"Certificate 4.3, L{target}: {c['in_region']} blocks in the region for H_j(B,t); {c['deferred']} require bounds by last-column class.")
        print(f"  At t=5, {c['deferred',5]} of {c['in_region',5]} blocks require bounds by last-column class.")
        print(f"  Of {c['coarse_residues']} candidate residues mod 24, {c['incompatible_at_three']} have no maximal lift at three.")
        print(f"  Locally compatible: {compatible-high} bounded below D0; {high} retained and bounded by U(B).")
        print(f"  Surviving last-column classes: {c['surviving_coarse_residues']} across {c['retained_blocks']} blocks.")
        print(f"  Bounded lifts: {c['bounded_lifts']}; ternary Gram matrices tested individually: {sum(row[0]==target for row in sources)}.")


if __name__=="__main__":
    main()
