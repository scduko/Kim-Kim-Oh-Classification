"""Export the binary-block search results for Certificate 4.3(a–c)."""
import argparse
import base64
from concurrent.futures import ProcessPoolExecutor
import gzip
import json
from pathlib import Path
import sys

from certificate_files import BLOCK_PAIRS, LAST_COLUMN_BOUNDS, GRAM_MATRICES, refresh_lean_input

HERE = Path(__file__).resolve().parent


def generate_slice(job):
    from bounded_exact import TARGET_HOSTS, bounds, ceil_div
    from scalar_sieve import ranges
    from block_filter import classify_range
    from collections import Counter

    target, start, stop = job
    intervals = ranges(TARGET_HOSTS[target][0])
    retained = []
    block_records = []
    for a in range(start, stop):
        for t, low, high in intervals.get(a, ()):
            codes = bytearray()
            for binary, delta in classify_range(TARGET_HOSTS[target][0], a, t, low, high, Counter(), codes):
                _, b, c = binary
                bound = bounds(target,binary,delta,ceil_div(3*delta**2,4*a))
                if bound:
                    upper_det, remaining = bound
                    # At two the mixed entries need only be known modulo four.
                    # At three the last column has modulus three. Thus record
                    # the mixed entries modulo 12 and the last norm modulo 24.
                    survivors = {((d%12)*12+e%12)*24+f for (d,e), fs in remaining.items() for f in fs}
                    if sum(map(len,remaining.values())) != 4*len(survivors):
                        raise ArithmeticError("mixed-entry period mismatch")
                    bits = sum(1 << i for i in survivors)
                    retained.append([target,a,b,c,upper_det,format(bits,"x")])
            block_records.append([target,a,t,base64.b64encode(codes).decode("ascii")])
    return retained, block_records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--verification",type=Path,default=HERE.parent/"verification")
    parser.add_argument("--output",type=Path,default=LAST_COLUMN_BOUNDS)
    parser.add_argument("--sources",type=Path,default=GRAM_MATRICES)
    parser.add_argument("--blocks", type=Path, default=BLOCK_PAIRS)
    args=parser.parse_args()
    sys.path.insert(0,str(args.verification.resolve()))
    from scalar_sieve import ranges
    from bounded_exact import TARGET_HOSTS
    stops={target:max(ranges(host))+1 for target,(host,_) in TARGET_HOSTS.items()}
    jobs=[(target,a,min(a+8,stop)) for target,stop in stops.items() for a in range(2,stop,8)]
    from block_filter import block_profiles,worst_steps
    for host in (3,9):
        for p in (2,3):
            block_profiles(host,p)
            worst_steps(host,p)
    rows,blocks=[],[]
    with ProcessPoolExecutor(args.workers) as pool:
        for group, certificates in pool.map(generate_slice,jobs):
            rows.extend(group)
            blocks.extend(certificates)
    rows.sort()
    blocks.sort()
    args.blocks.write_bytes(gzip.compress(json.dumps(blocks,separators=(",",":")).encode("ascii"),mtime=0))
    data=json.dumps(rows,separators=(",",":")).encode()
    args.output.write_bytes(gzip.compress(data,mtime=0))
    from coverage_sources import source_rows
    sources = sorted(row for target,a,b,c,upper_det,hex_bits in rows
                     for row,passes in source_rows(target,a,b,c,upper_det,int(hex_bits,16)) if passes)
    if len(sources)!=len(set(sources)):
        raise ValueError("duplicate terminal source")
    text="".join(" ".join(map(str,row))+"\n" for row in sources)
    args.sources.write_bytes(gzip.compress(text.encode("ascii"),mtime=0))
    refresh_lean_input(args.output)
    print(f"Exported {len(rows)} binary blocks and {len(sources)} terminal sources.")


if __name__=="__main__":
    main()
