#!/usr/bin/env python3
"""Print the modules of `KimKimOh` that do not depend on a generated kernel check.

CI builds exactly these modules. A module is excluded when it is a generated file (header
`-- Generated`) with a `decide +kernel` check, other than the acceptance tables
(`Tables/Check*`): the checks of the profiles (`Tables/ProfCheck*`), of the first pass (`FirstPassChecks/Enum*`) and
of the last-column test (`Terminal/`), or when it imports such a module, directly or indirectly
(for example `KimKimOh.HostData`, `KimKimOh.Main` and the root `KimKimOh`). The output is in
dependency order. Every module must be reachable from the root `KimKimOh`.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def path_of(mod):
    return os.path.join(ROOT, *mod.split(".")) + ".lean"


def imports(mod):
    with open(path_of(mod), encoding="utf-8") as f:
        text = f.read()
    return [m for m in re.findall(r"^import\s+(\S+)", text, re.M) if m.startswith("KimKimOh")]


# The acceptance tables at 2 and 3 are checked in CI: nearly every module imports them.
LIGHT_CHECKS = ("KimKimOh.Tables.Check",)


def is_check(mod):
    with open(path_of(mod), encoding="utf-8") as f:
        text = f.read()
    return (text.startswith("-- Generated") and "decide +kernel" in text
            and not mod.startswith(LIGHT_CHECKS))


def main():
    order, seen = [], set()

    def visit(mod):
        if mod in seen:
            return
        seen.add(mod)
        for dep in imports(mod):
            visit(dep)
        order.append(mod)

    visit("KimKimOh")
    heavy = {}
    for mod in order:
        heavy[mod] = is_check(mod) or any(heavy[d] for d in imports(mod))
    for mod in order:
        if not heavy[mod]:
            print(mod)


if __name__ == "__main__":
    sys.exit(main())
