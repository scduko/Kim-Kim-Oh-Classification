"""Certificate 4.3(c) and Table 4: enumerate the lifts in the surviving last-column classes."""
from functools import cache
from itertools import product
from math import gcd


def ceil_div(n, d):
    return -((-n)//d)


def residue_index(d, e, f):
    """Mixed entries modulo 12, diagonal entry modulo 24, in lexicographic order."""
    return ((d % 12)*12 + e % 12)*24 + f % 24


@cache
def maximal_at_three(gram_mod_9):
    """Rule out each of the 13 possible projective generators z/3."""
    a,b,c,d,e,f = gram_mod_9
    for x,y,z in product(range(3), repeat=3):
        if next((u for u in (x,y,z) if u),0)!=1:
            continue
        # Adjoining v/3 preserves integral pairings if Gv vanishes mod 3,
        # and gives it integral norm if v^T Gv vanishes mod 9.
        image = (a*x+b*y+d*z, b*x+c*y+e*z, d*x+e*y+f*z)
        if all(u%3==0 for u in image):
            if (x*image[0]+y*image[1]+z*image[2])%9==0:
                return False
    return True


def source_rows(target, a, b, c, upper_det, survivor_bits):
    """Enumerate lifts with D0 <= det(G) <= upper_det in the surviving classes.

    Yield the Gram entries and a flag indicating whether this lift needs
    an individual witness. All lifts count toward the bounded-lift total.
    """
    delta = a*c-b*b
    D0 = ceil_div(3*delta*delta,4*a)
    for d in range(a//2+1):
        e_low = ceil_div(2*b*d-delta,2*a)
        e_high = (2*b*d+delta)//(2*a)
        if d==0:
            e_low = max(0,e_low)
        if b==0 or 2*b==a:
            e_low = max(e_low,ceil_div(b*d,a))
        for e in range(e_low, e_high+1):
            f_bits = (survivor_bits >> residue_index(d,e,0)) & ((1<<24)-1)
            if not f_bits:
                continue
            # For fixed last-column entries d,e, det(G) = delta*f - block_form.
            # Intersect its determinant interval with the reduced-basis bounds.
            block_form = c*d*d-2*b*d*e+a*e*e
            low = max(a,ceil_div(delta+d*d,a),ceil_div(D0+block_form,delta))
            high = (upper_det+block_form)//delta
            for residue in range(24):
                if (f_bits >> residue) & 1:
                    for f in range(low+(residue-low)%24,high+1,24):
                        gram = (a,b,c,d,e,f)
                        passes = gcd(*gram)==1 and maximal_at_three(tuple(v%9 for v in gram))
                        yield (target,*gram),passes
