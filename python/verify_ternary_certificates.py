"""Verify Certificates 4.1–4.3 for the ternary universality of L6 and L9 against the supplied records."""
import argparse
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=1,
                        help="number of processes for checking the binary blocks")
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    audit = Path(__file__).resolve().parent / "audit"
    for name, options in [
        ("verify_steps_and_ranges.py", ["--verify-tables"]),
        ("verify_block_coverage.py", ["--workers", str(args.workers)]),
        ("verify_representation_witnesses.py", []),
    ]:
        subprocess.run([sys.executable, str(audit / name), *options], check=True)
    print("All certificate checks passed.")


if __name__ == "__main__":
    main()
