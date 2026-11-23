#!/usr/bin/env python3
"""Build or replay one part of the modules that depend on a generated kernel check of §4.

The full verification workflow splits these modules, in dependency order,
into PARTS contiguous parts of about equal estimated cost, so that each part fits one job of a
hosted runner; a module's imports are then in its own part or an earlier one. The estimates are
the wall times of the clean-room build (`scripts/module_costs.json`; a module missing there
counts 60 seconds). Part 0 is the light modules (`scripts/ci_modules.py`).

  python3 scripts/full_build.py check       check that the parts cover all first-party release files
  python3 scripts/full_build.py list K      print the modules of part K
  python3 scripts/full_build.py build K     build them one at a time (at most one Lean process,
                                            so that a module of 9 GB fits a 16 GB runner)
  python3 scripts/full_build.py replay K    replay each named module from its imports
"""
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PARTS = 4


def imports(mod):
    with open(os.path.join(ROOT, *mod.split('.')) + '.lean', encoding='utf-8') as f:
        return [m for m in re.findall(r'^import\s+(\S+)', f.read(), re.M) if m.startswith('KimKimOh')]


def order():
    out, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for d in imports(m):
            visit(d)
        out.append(m)
    visit('KimKimOh')
    return out


def parts():
    light = subprocess.check_output([sys.executable, os.path.join(ROOT, 'scripts', 'ci_modules.py')],
                                    text=True).split()
    lightset = set(light)
    modules = order()
    heavy = [m for m in modules if m not in lightset]
    path = os.path.join(ROOT, 'scripts', 'module_costs.json')
    costs = json.load(open(path)) if os.path.exists(path) else {}
    cost = [float(costs.get(m, 60)) for m in heavy]
    total, res, cur, acc = sum(cost), [light], [], 0.0
    for m, c in zip(heavy, cost):
        # close the current part once it holds its share of the total
        if cur and len(res) < PARTS and acc + c / 2 > total * len(res) / PARTS:
            res.append(cur)
            cur = []
        cur.append(m)
        acc += c
    res.append(cur)
    while len(res) < PARTS + 1:
        res.append([])
    assigned = [module for part in res for module in part]
    if len(assigned) != len(modules) or set(assigned) != set(modules):
        raise ValueError('the parts must contain every module imported by KimKimOh, including the root, exactly once')
    return res


def main():
    if sys.argv[1:] == ['check']:
        root = Path(ROOT)
        sources = [root / 'KimKimOh.lean', *(root / 'KimKimOh').rglob('*.lean')]
        on_disk = {'.'.join(p.relative_to(root).with_suffix('').parts) for p in sources}
        assigned = {module for group in parts() for module in group}
        if on_disk != assigned:
            raise SystemExit(f'unassigned sources: {sorted(on_disk - assigned)}; '
                             f'assignments without sources: {sorted(assigned - on_disk)}')
        print(f'All {len(on_disk)} first-party release modules are assigned exactly once.')
        return
    if len(sys.argv) != 3 or sys.argv[1] not in ('list', 'build', 'replay'):
        raise SystemExit(__doc__)
    k = int(sys.argv[2])
    if not 0 <= k <= PARTS:
        raise SystemExit(f'part must be between 0 and {PARTS}')
    mods = parts()[k]
    if sys.argv[1] == 'list':
        print('\n'.join(mods))
        return
    if sys.argv[1] == 'replay':
        t0 = time.time()
        for i, module in enumerate(mods, 1):
            print(f'[{i}/{len(mods)}] Replaying {module}', flush=True)
            subprocess.run(['lake', 'env', 'lean', '--run', 'scripts/ReplayModule.lean', module],
                           cwd=ROOT, check=True)
        print(f'replayed {len(mods)} modules in {time.time() - t0:.0f} s', flush=True)
        return
    env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get('LEAN_NUM_THREADS', '2'))
    for i, m in enumerate(mods):
        t0 = time.time()
        r = subprocess.run(['lake', 'build', m], cwd=ROOT, env=env)
        print(f'[{i + 1}/{len(mods)}] {m}: {time.time() - t0:.0f} s', flush=True)
        if r.returncode:
            sys.exit(r.returncode)


if __name__ == '__main__':
    main()
