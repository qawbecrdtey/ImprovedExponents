#!/usr/bin/env bash
# upstream/3sum-apsp/ holds the part of the Lean formalization anthropics/formal-math, directory
# 3sum-apsp, at the commit below, that this project uses (Copyright (c) 2026 Anthropic, PBC, Apache
# License 2.0), ported to Lean and Mathlib v4.35.0-rc2. This script fetches that commit and confirms,
# file by file, that every file of upstream/3sum-apsp/ is upstream's file of the same path, and either
#
#   * identical to it, or
#   * listed in upstream/README.md as changed by the port, with the line NOTICE_LINE below in its header;
#
# that every file listed there is indeed changed; that LICENSE, NOTICE and EndStatement.lean (the
# trusted statements, copied verbatim into ImprovedChallenge.lean) are identical to upstream's; that
# every entry of upstream/3sum-apsp/ is a regular file or a directory; that its files of Lean are
# exactly those that this project imports, directly or transitively; and that the counts stated in
# the paper (\UpstreamFiles and \UpstreamChanged in papers/improved-exponents/results.tex) are these.
#
#     scripts/check-upstream.sh                     # from anywhere; needs git, python3 and network
#     UPSTREAM_GIT=<repo> scripts/check-upstream.sh  # a local clone of anthropics/formal-math instead
set -euo pipefail
if [ -n "${UPSTREAM_GIT:-}" ]; then
  UPSTREAM_GIT="$(cd "$UPSTREAM_GIT" && pwd)"
fi
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

# Every entry is a regular file or a directory: no symbolic link or other file can stand in for one.
while IFS= read -r path; do
  fail "$ours/$path: not a regular file"
done < <(cd "$ours" && find . -mindepth 1 \( -type l -o ! \( -type f -o -type d \) \) | sed 's|^\./||' | sort)

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

# The files of Lean are exactly the import closure of the project's own modules, and the paper's
# counts of the included and of the changed files are right.
python3 - "$ours" "$changed" <<'EOF' || failed=1
import pathlib, re, sys

ours, changed = pathlib.Path(sys.argv[1]), int(sys.argv[2])
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", re.M)
ROOTS = ("ThreeSumApsp", "EndStatement", "PaperStatements")


def imports(path):
    return [m for m in IMPORT.findall(path.read_text(encoding="utf-8")) if m.split(".")[0] in ROOTS]


own = [*pathlib.Path("ImprovedExponents").rglob("*.lean"),
       *map(pathlib.Path, ["ImprovedExponents.lean", "ImprovedChallenge.lean", "ImprovedSolution.lean"])]
todo = [m for path in own for m in imports(path)]
closure, missing = set(), set()
while todo:
    module = todo.pop()
    if module in closure or module in missing:
        continue
    path = ours / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        missing.add(module)
        continue
    closure.add(module)
    todo += imports(path)
included = {str(p.relative_to(ours))[:-5].replace("/", ".") for p in ours.rglob("*.lean")}

ok = True
for module in sorted(missing):
    print(f"{ours}: {module} is imported but not included", file=sys.stderr)
    ok = False
for module in sorted(included - closure):
    print(f"{ours}: {module} is included but nothing in the project imports it", file=sys.stderr)
    ok = False
results = pathlib.Path("papers/improved-exponents/results.tex").read_text(encoding="utf-8")
for macro, value in (("UpstreamFiles", len(included)), ("UpstreamChanged", changed)):
    found = re.search(r"\\newcommand\{\\" + macro + r"\}\{([^}]*)\}", results)
    if not found or found.group(1) != str(value):
        print(f"papers/improved-exponents/results.tex: \\{macro} must be {value}", file=sys.stderr)
        ok = False
sys.exit(0 if ok else 1)
EOF

[ "$failed" -eq 0 ] || die "upstream/3sum-apsp does not match anthropics/formal-math $COMMIT as recorded"
echo "upstream/3sum-apsp: $((same + changed)) files of anthropics/formal-math $COMMIT (3sum-apsp):" \
  "$same identical, $changed changed by the port and listed in $readme;" \
  "its files of Lean are exactly the import closure of the project"
