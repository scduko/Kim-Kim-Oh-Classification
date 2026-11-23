"""Certificate 4.3(c): find a coefficient column witnessing representation of each bounded matrix."""
from functools import cache
from itertools import product
from math import gcd

from local_representation import radical_lines, represents, residues, source_flags
from notation import TARGET_HOSTS


@cache
def prime_factors_from_five(n):
    """Distinct prime factors at least five, in increasing order."""
    if n < 1:
        raise ValueError("factorization requires a positive integer")
    result = []
    for p in (2,3):
        while n % p == 0:
            n //= p
    p = 5
    while p*p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 2
    if n > 1:
        result.append(n)
    return tuple(result)


def enlargements(gram,p):
    """Adjoin each integral z/p, using its first nonzero coordinate to select the replaced basis vector."""
    a,b,c,d,e,f = gram
    rows = ((a,b,d),(b,c,e),(d,e,f))
    for z in radical_lines(p,tuple(t%p for t in gram)):
        gz = tuple(sum(t*u for t,u in zip(row,z)) for row in rows)
        norm = sum(t*u for t,u in zip(gz,z))
        if norm % (p*p):
            continue
        i = z.index(1)
        result = [list(row) for row in rows]
        for j in range(3):
            result[i][j] = result[j][i] = gz[j]//p
        result[i][i] = norm//(p*p)
        yield z, tuple(result[h][j] for h,j in ((0,0),(0,1),(1,1),(0,2),(1,2),(2,2)))


def locally_embeds(host,p,gram):
    return represents(host,p,gram) or any(represents(host,p,larger) for _,larger in enlargements(gram,p))


ENTRIES = ((0,0),(0,1),(1,1),(0,2),(1,2),(2,2))
# After the maximum norm, use the sum of absolute values and then lexicographic order.
VECTORS = sorted(product(range(-2,3),repeat=3),
                 key=lambda v: (max(map(abs,v)),sum(map(abs,v)),v))


def locally_represented(host, gram):
    if not all(locally_embeds(host,p,gram) for p in (2,3)):
        return False
    a,b,c,d,e,f = gram
    # These are the six distinct 2-by-2 minors, up to sign. A prime can
    # reduce the rank below two only if it divides them all (Lemma 2.1).
    minor_gcd = gcd(a*c-b*b, a*e-b*d, c*d-b*e, a*f-d*d, b*f-d*e, c*f-e*e)
    for p in prime_factors_from_five(minor_gcd):
        if not any(pow(host*n%p,(p-1)//2,p)==1 for n in (a,c,f)):
            return False
    return True


def find(target, gram):
    host,scale = TARGET_HOSTS[target]
    for vector in VECTORS:
        corrected_gram = tuple(n-scale*vector[i]*vector[j] for n,(i,j) in zip(gram,ENTRIES))
        a,b,c,d,e,f = corrected_gram
        # Sylvester's criterion for the corrected ternary Gram matrix.
        Delta = a*c - b*b
        if a > 0 and Delta > 0 and Delta*f - c*d*d + 2*b*d*e - a*e*e > 0:
            if locally_represented(host,corrected_gram):
                return vector
    return None


def certify_range(target, binary, d, e, start, top, counts):
    a,b,c = binary
    index = residues(3).encode(a%9, b%9, c%9, d%9, e%9, 0)
    source_at_three = source_flags(3)
    for f in range(start,top+1,24):
        gram = binary + (d,e,f)
        if not source_at_three[index+f%9] or gcd(*gram) != 1:
            continue
        counts["tested"] += 1
        witness = find(target,gram)
        if witness is None:
            raise ArithmeticError(("no certified covector",target,gram))
        counts[max(map(abs,witness))] += 1
