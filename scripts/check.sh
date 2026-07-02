#!/usr/bin/env bash
# Check a unit: no sorries in its files, and it builds.
# Usage: scripts/check.sh Jacobian/Cech      (a unit directory or a single .lean file)
#        scripts/check.sh                    (whole project)
set -u
cd "$(dirname "$0")/.."
target="${1:-Jacobian}"
target="${target%.lean}"
target="${target%/}"

paths=()
[ -d "$target" ] && paths+=("$target")
[ -f "$target.lean" ] && paths+=("$target.lean")
if [ ${#paths[@]} -eq 0 ]; then echo "no such unit: $target"; exit 2; fi

if grep -rn --include='*.lean' -w 'sorry' "${paths[@]}"; then
  echo "FAIL: sorries found (listed above)"
  exit 1
fi

module="${target//\//.}"
if lake build "$module" 2>&1 | tail -40; then
  echo "OK: $module builds, no sorries"
else
  echo "FAIL: build errors in $module"
  exit 1
fi
