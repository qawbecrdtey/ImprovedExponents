#!/usr/bin/env bash
# The statement module ImprovedChallenge.lean imports nothing; it contains a verbatim copy of the
# trusted file EndStatement.lean of the upstream formalization (anthropics/formal-math, 3sum-apsp).
# This script confirms that the copy, from the documentation comment «Claims of the paper …» to the
# line «end EndStatement», is byte for byte the corresponding part of upstream/3sum-apsp/EndStatement.lean,
# which scripts/check-upstream.sh in turn confirms to be upstream's file, unmodified.
#
#     scripts/check-endstatement.sh      # from anywhere; no build and no network needed
set -euo pipefail
project="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project"
upstream=upstream/3sum-apsp/EndStatement.lean
[ -f "$upstream" ] || { echo "error: $upstream is missing" >&2; exit 1; }

extract() { sed -n '/^\/-! Claims of the paper/,/^end EndStatement$/p' "$1"; }
ours="$(extract ImprovedChallenge.lean)"
theirs="$(extract "$upstream")"
[ -n "$ours" ] || { echo "error: the block was not found in ImprovedChallenge.lean" >&2; exit 1; }
if [ "$ours" != "$theirs" ]; then
  echo "error: the copy of EndStatement.lean in ImprovedChallenge.lean differs from $upstream:" >&2
  diff <(printf '%s\n' "$theirs") <(printf '%s\n' "$ours") >&2 || true
  exit 1
fi
lines="$(printf '%s\n' "$ours" | wc -l)"
echo "ImprovedChallenge.lean: the $lines lines of EndStatement.lean are identical to $upstream"
