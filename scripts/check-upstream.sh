#!/usr/bin/env bash
# upstream/3sum-apsp/ holds the part of the Lean formalization anthropics/formal-math, directory
# 3sum-apsp, at the commit below, that this project uses (Copyright (c) 2026 Anthropic, PBC, Apache
# License 2.0), ported to Lean and Mathlib v4.35.0-rc2. This script fetches that commit and confirms,
# file by file, that every file of upstream/3sum-apsp/ is upstream's file of the same path, and either
#
#   * identical to it, or
#   * listed in upstream/README.md as changed by the port, with the line NOTICE_LINE below in its header;
#
# that every file listed there is indeed changed; and that LICENSE, NOTICE and EndStatement.lean (the
# trusted statements, copied verbatim into ImprovedChallenge.lean) are identical to upstream's.
#
#     scripts/check-upstream.sh                     # from anywhere; needs git and network access
#     UPSTREAM_GIT=<repo> scripts/check-upstream.sh  # a local clone of anthropics/formal-math instead
set -euo pipefail
project="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project"

URL=https://github.com/anthropics/formal-math
COMMIT=e1a4e6508154ea59f030480661590a9fe3018011
NOTICE_LINE='Modified in 2026 for ImprovedExponents (Jihoon Hyun): ported to Lean and Mathlib v4.35.0-rc2.'
VERBATIM=(LICENSE NOTICE EndStatement.lean)
ours=upstream/3sum-apsp
readme=upstream/README.md

die() { echo "error: $*" >&2; exit 1; }
[ -d "$ours" ] || die "$ours is missing"
[ -f "$readme" ] || die "$readme is missing"
grep -qF "$COMMIT" "$readme" || die "$readme does not name the commit $COMMIT"

work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
repo="${UPSTREAM_GIT:-}"
if [ -z "$repo" ]; then
  repo="$work/repo"
  git init --quiet "$repo"
  git -C "$repo" fetch --quiet --depth 1 "$URL" "$COMMIT"
fi
mkdir "$work/src"
git -C "$repo" archive "$COMMIT" 3sum-apsp | tar -x -C "$work/src"
theirs="$work/src/3sum-apsp"

# The files that upstream/README.md lists as changed: the lines «- `path`: …» between the two markers.
listed="$(sed -n '/^<!-- changed files: begin -->$/,/^<!-- changed files: end -->$/p' "$readme" \
  | sed -n 's/^- `\([^`]*\)`.*/\1/p' | sort)"

failed=0
fail() { echo "$*" >&2; failed=1; }
same=0; changed=0
while IFS= read -r path; do
  if [ ! -f "$theirs/$path" ]; then
    fail "$ours/$path: not a file of upstream at $COMMIT"
  elif cmp -s "$ours/$path" "$theirs/$path"; then
    same=$((same + 1))
    grep -qxF "$path" <<<"$listed" && fail "$ours/$path: listed in $readme as changed, but identical to upstream"
    grep -qF "$NOTICE_LINE" "$ours/$path" && fail "$ours/$path: marked as modified, but identical to upstream"
  else
    changed=$((changed + 1))
    grep -qxF "$path" <<<"$listed" || fail "$ours/$path: differs from upstream, but is not listed in $readme"
    head -n 12 "$ours/$path" | grep -qxF "$NOTICE_LINE" \
      || fail "$ours/$path: differs from upstream, but its header lacks the line «$NOTICE_LINE»"
  fi
done < <(cd "$ours" && find . -type f | sed 's|^\./||' | sort)

while IFS= read -r path; do
  [ -z "$path" ] || [ -f "$ours/$path" ] || fail "$readme lists $path, which is not in $ours"
done <<<"$listed"
for path in "${VERBATIM[@]}"; do
  cmp -s "$ours/$path" "$theirs/$path" || fail "$ours/$path: must be identical to upstream"
done

[ "$failed" -eq 0 ] || die "upstream/3sum-apsp does not match anthropics/formal-math $COMMIT as recorded"
echo "upstream/3sum-apsp: $((same + changed)) files of anthropics/formal-math $COMMIT (3sum-apsp):" \
  "$same identical, $changed changed by the port and listed in $readme"
