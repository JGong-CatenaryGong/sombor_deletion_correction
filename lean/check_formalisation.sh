#!/usr/bin/env bash
# Verify the formalisation: build with no `sorry`, and report the theorem inventory.
set -uo pipefail
cd "$(dirname "$0")"
export ELAN_HOME="$(cd .. && pwd)/.elan"
export PATH="$ELAN_HOME/bin:$PATH" ELAN_NO_RCFILE=1
export XDG_CACHE_HOME="$PWD/.cache"
echo "=== lake build ==="
if ! lake build 2>&1 | tail -2; then
  echo "LAKE BUILD FAILED"
  exit 1
fi
echo "=== sorry / admit check ==="
if ! python3 check_sorry.py ; then
  exit 1
fi
echo "=== theorem inventory ==="
grep -h -E "^theorem |^lemma " StarTheorem/*.lean | wc -l
