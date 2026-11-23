#!/usr/bin/env bash
# A parent and its descendant must be independently replayable by exact name.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d "$root/replay-test.XXXXXX")
trap 'rm -rf "$work"' EXIT
cd "$work"
export LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
mkdir ReplayCase
echo 'theorem parent_ok : True := True.intro' > ReplayCase.lean
printf '%s\n' 'module' 'public theorem support_ok : True := True.intro' > ReplaySupport.lean
printf '%s\n' 'module' 'import ReplaySupport' 'private theorem child_ok : True := support_ok' > ReplayCase/Child.lean
for file in ReplaySupport ReplayCase ReplayCase/Child; do
  lean -o "$file.olean" "$file.lean"
done
replay() { lean --run "$root/scripts/ReplayModule.lean" "$1"; }
replay ReplayCase.Child
# A missing import makes the child unreplayable. Its parent must still succeed.
rm ReplaySupport.olean
replay ReplayCase
if replay ReplayCase.Child; then echo 'Unexpected success with a missing import' >&2; exit 1; fi
if replay ReplayCase.Missing; then echo 'Unexpected success for an absent module' >&2; exit 1; fi
