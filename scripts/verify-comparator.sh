#!/usr/bin/env bash
# Judge ImprovedSolution against ImprovedChallenge the way the Palomar registry does: with the
# `lake comparator` that ships in the project's toolchain (v4.35.0-rc2; the registry requires
# v4.35.0-rc2 or later). It rebuilds both modules in a bubblewrap sandbox, exports them, checks
# that every theorem named in comparator.json has the same statement on both sides and uses no
# axiom outside the permitted list, and replays the solution through Lean's kernel and the
# toolchain's bundled independent kernels NanoDa and con-ron. Adapted from
# PalomarRegistry/PalomarTemplate, scripts/verify-comparator.sh.
#
#     scripts/verify-comparator.sh                 # from anywhere; needs bwrap, git and rsync
#     scripts/verify-comparator.sh --paranoid      # also leanchecker-paranoid, lean4lean, con-leche
#
# The run happens in a fresh copy of the sources, as in a fresh clone: the files tracked by git (as
# they are in the working tree), with no build products, so that `lake comparator` compiles the
# challenge, the solution and everything that they import inside its sandbox instead of finding
# them built. The copy is $COMPARATOR_RUNS/ImprovedExponents (default ~/comparator-runs); its
# dependencies (.lake/packages: Mathlib from `lake exe cache get`, and the rest of its set) are
# synchronized from the project rather than copied anew, and everything else in it is replaced on
# every run. The log of the run is $COMPARATOR_RUNS/comparator-<time>.log.
#
# Palomar ignores `enable_nanoda` and rejects `external_kernels` in a submitted comparator.json: it
# registers the toolchain's bundled kernels itself. This script does the same in a generated copy of
# the configuration, so that the local check judges as the registry does. Nothing here is a
# verifier pin: everything that judges comes from lean-toolchain.
#
# The sandbox of `lake comparator` covers /run/user with a tmpfs, which fails on a host that has no
# /run/user (OpenRC without elogind, some containers). There the run is wrapped in a further
# namespace whose /run is the host's with an empty /run/user added (bwrap 0.10 or later); nothing
# else changes. Alternatively, create the directory: `sudo mkdir /run/user`.
set -euo pipefail
project="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project"

die() { echo "error: $*" >&2; exit 1; }
for required in bwrap git rsync lake lean python3; do
  command -v "$required" >/dev/null 2>&1 || die "$required is required (bwrap: see scripts/install-bwrap.sh)"
done
git rev-parse --is-inside-work-tree >/dev/null 2>&1 || die "$project is not a git checkout"
toolchain="$(tr -d '[:space:]' < lean-toolchain)"
prefix="$(lean --print-prefix)"
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  [ -x "$prefix/bin/$tool" ] || die "toolchain $toolchain does not bundle $tool; Palomar requires leanprover/lean4:v4.35.0-rc2 or later"
done

runs="${COMPARATOR_RUNS:-$HOME/comparator-runs}"
mkdir -p "$runs"
runs="$(cd "$runs" && pwd)"
run="$runs/ImprovedExponents"
marker="$run/.verify-comparator-copy"
log="$runs/comparator-$(date -u +%Y%m%dT%H%M%SZ).log"

wrap=()
if [ ! -d /run/user ]; then
  bwrap --help 2>&1 | grep -q -- '--tmp-overlay' \
    || die "/run/user is missing and this bwrap has no --tmp-overlay (0.10 or later): sudo mkdir /run/user"
  wrap=(bwrap --dev-bind / / --overlay-src /run --tmp-overlay /run --dir /run/user --)
fi

main() {
  set -e
  echo "toolchain: $toolchain"
  echo "sources: commit $(git rev-parse HEAD)$( [ -z "$(git status --porcelain --untracked-files=no)" ] \
    || echo ", with uncommitted changes to tracked files")"
  echo "copy: $run (tracked files only, no build products)"
  [ "${#wrap[@]}" -eq 0 ] \
    || echo "note: no /run/user on this host; lake comparator runs inside: ${wrap[*]}"
  echo "started: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "config: comparator.json"
  cat comparator.json

  # The dependencies, in the project (fetched if missing), then synchronized into the copy.
  lake exe cache get
  if [ -e "$run" ] && [ ! -e "$marker" ]; then
    die "$run exists but was not made by this script; remove it or set COMPARATOR_RUNS"
  fi
  mkdir -p "$run/.lake/packages"
  touch "$marker"
  find "$run" -mindepth 1 -maxdepth 1 ! -name .lake ! -name "$(basename "$marker")" -exec rm -rf -- {} +
  find "$run/.lake" -mindepth 1 -maxdepth 1 ! -name packages -exec rm -rf -- {} +
  packages="$(python3 -c '
import json, sys
print("\n".join(p["name"] for p in json.load(open(sys.argv[1]))["packages"]))' lake-manifest.json)"
  find "$run/.lake/packages" -mindepth 1 -maxdepth 1 | while IFS= read -r dir; do
    grep -qxF "$(basename "$dir")" <<<"$packages" || rm -rf -- "$dir"
  done
  while IFS= read -r name; do
    [ -d ".lake/packages/$name" ] || die "the dependency $name is missing from .lake/packages"
    rsync -a --delete ".lake/packages/$name/" "$run/.lake/packages/$name/"
  done <<<"$packages"
  # The sources: the files tracked by git, as they are in the working tree.
  git ls-files -z | rsync -a --from0 --files-from=- --ignore-missing-args ./ "$run/"

  local config
  config="$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")"
  python3 - comparator.json "$config" "$prefix" <<'PY'
import json, pathlib, sys
source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
assert isinstance(config, dict), "comparator.json must contain one JSON object"
assert "external_kernels" not in config, "external_kernels is not a submitter field; Palomar rejects it"
assert set(config["permitted_axioms"]) <= {"propext", "Quot.sound", "Classical.choice"}, "permitted_axioms"
config.pop("enable_nanoda", None)
config["external_kernels"] = {"nanoda": [f"{prefix}/bin/nanoda_bin"], "con-ron": [f"{prefix}/bin/con-ron"]}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

  echo "== lake comparator --config comparator.json (toolchain $toolchain) $*"
  local status=0
  (cd "$run" && ${wrap[@]+"${wrap[@]}"} lake comparator --config "$config" "$@") || status=$?
  rm -f "$config"
  echo "finished: $(date -u +%Y-%m-%dT%H:%M:%SZ), exit status $status"
  return "$status"
}

set +e
main "$@" 2>&1 | tee "$log"
status="${PIPESTATUS[0]}"
set -e
if [ "$status" -eq 0 ] && grep -qxF 'Your solution is okay!' "$log"; then
  echo "PASS (log: $log)"
else
  die "lake comparator did not accept comparator.json (exit status $status; log: $log)"
fi
