#!/usr/bin/env bash
# The statement module ImprovedChallenge.lean imports nothing; it contains a verbatim copy of the
# trusted file EndStatement.lean of the upstream formalization (anthropics/formal-math, 3sum-apsp).
# This script confirms that the copy, from the documentation comment «Claims of the paper …» to the
# line «end EndStatement», is byte for byte the corresponding part of the dependency that Lake
# fetched, and that the dependency is at the commit named in lake-manifest.json.
#
#     scripts/check-endstatement.sh      # after `lake build` (or `lake update`), from anywhere
set -euo pipefail
project="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project"
upstream=.lake/packages/ThreeSumApsp/3sum-apsp/EndStatement.lean
[ -f "$upstream" ] || { echo "error: $upstream is missing; run 'lake build' first" >&2; exit 1; }

extract() { sed -n '/^\/-! Claims of the paper/,/^end EndStatement$/p' "$1"; }
ours="$(extract ImprovedChallenge.lean)"
theirs="$(extract "$upstream")"
[ -n "$ours" ] || { echo "error: the block was not found in ImprovedChallenge.lean" >&2; exit 1; }
if [ "$ours" != "$theirs" ]; then
  echo "error: the copy of EndStatement.lean in ImprovedChallenge.lean differs from the dependency:" >&2
  diff <(printf '%s\n' "$theirs") <(printf '%s\n' "$ours") >&2 || true
  exit 1
fi
lines="$(printf '%s\n' "$ours" | wc -l)"

wanted="$(python3 -c '
import json, sys
for p in json.load(open("lake-manifest.json"))["packages"]:
    if p["name"] == "ThreeSumApsp": print(p["rev"])
')"
actual="$(git -C .lake/packages/ThreeSumApsp rev-parse HEAD)"
if [ "$wanted" != "$actual" ]; then
  echo "error: the dependency is at $actual, the manifest names $wanted" >&2; exit 1
fi
echo "ImprovedChallenge.lean: the $lines lines of EndStatement.lean are identical to the dependency's (anthropics/formal-math $actual)"
