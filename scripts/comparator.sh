#!/usr/bin/env bash
# Run the tool Comparator (leanprover/comparator) on this project's challenge/solution pair, with the
# standalone tools at the releases for the project's toolchain. This is the check for the
# toolchain of this project, v4.33.1; from Lean v4.35.0-rc2 on, Comparator ships inside the toolchain
# as `lake comparator`, which scripts/verify-comparator.sh runs (and which the Palomar registry uses).
#
# Comparator checks that every theorem of `ImprovedSolution` named in `comparator.json` has exactly the
# statement of its namesake in `ImprovedChallenge` (which imports nothing and has `sorry` for every
# proof), that the proofs use only the permitted axioms, and that everything replays in Lean's kernel
# and in the independent kernel nanoda. It builds both modules inside the Landlock sandbox landrun
# and reads them with lean4export.
#
#     scripts/comparator.sh install   # build the tools (no root; about 2 GB) into $COMPARATOR_TOOLS
#     scripts/comparator.sh run       # copy the project to a fresh directory and run Comparator there
#     scripts/comparator.sh all       # both
#
# The script follows upstream's CI (anthropics/formal-math, .github/scripts/comparator-check.sh):
# nanoda and landrun are at the commits pinned there. Comparator and lean4export are at their tags
# v4.33.0 (neither has a tag v4.33.1), both built with the project's toolchain v4.33.1, so that the
# kernel replaying the solution inside Comparator is the project's Lean. Upstream instead pins
# comparator at 5756749 (after v4.34.0-rc1), which is built with its own toolchain v4.34.0-rc1; that
# commit also has later fixes, among them a check that the quotient constants survive the replay
# (comparator issue 71). Go is needed only to build landrun and is installed under the tools directory
# if it is not on the PATH.
#
# The run happens in a fresh copy of the sources (the project's own build directory and upstream's
# are left out; the compiled Mathlib from `lake exe cache get` is kept, as in CI), because the
# sandbox has no network and Comparator expects to compile the challenge and the solution itself.
# Success: exit status 0 and the line "Your solution is okay!"; the log is kept in the run directory.
set -euo pipefail

TOOLS="${COMPARATOR_TOOLS:-$HOME/opt/comparator-tools}"
RUNS="${COMPARATOR_RUNS:-$HOME/comparator-runs}"
PROJECT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CONFIG="${COMPARATOR_CONFIG:-comparator.json}"

COMPARATOR_COMMIT="${COMPARATOR_COMMIT:-3927ad383f208ae977c340a91c48ac9b497d2097}"  # tag v4.33.0
NANODA_COMMIT="${NANODA_COMMIT:-68d5ca9db226849b41a6fff59d796ff19d0a8840}"
LANDRUN_COMMIT="${LANDRUN_COMMIT:-811cfff51ceaf3d9843708aa6d22e9b84ccac8b4}"
LEAN4EXPORT_COMMIT="${LEAN4EXPORT_COMMIT:-15f6055e299ad5b89345e533cc2192f4cc00f659}"  # tag v4.33.0
GO_VERSION="${GO_VERSION:-1.27.1}"

die() { echo "error: $*" >&2; exit 1; }

checkout_at() {  # <url> <dir> <commit>
  if [ ! -d "$2/.git" ]; then
    git clone --quiet --filter=blob:none "$1" "$2"
  fi
  if [ "$(git -C "$2" rev-parse HEAD)" != "$3" ]; then
    git -C "$2" fetch --quiet --depth 1 origin "$3"
    git -C "$2" checkout --quiet --detach "$3"
  fi
}

install_tools() {
  for tool in git cargo lean lake curl; do
    command -v "$tool" >/dev/null 2>&1 || die "$tool is required"
  done
  mkdir -p "$TOOLS/bin" "$TOOLS/dl"
  toolchain="$(tr -d '[:space:]' < "$PROJECT/lean-toolchain")"

  if ! command -v go >/dev/null 2>&1; then
    if [ ! -x "$TOOLS/go/bin/go" ]; then
      echo "== go $GO_VERSION (user-local, for landrun)"
      tarball="go$GO_VERSION.linux-amd64.tar.gz"
      (cd "$TOOLS/dl" && curl -fsSLO "https://dl.google.com/go/$tarball" \
        && curl -fsSLo "$tarball.sha256" "https://dl.google.com/go/$tarball.sha256" \
        && echo "$(tr -d '[:space:]' < "$tarball.sha256")  $tarball" | sha256sum -c -)
      rm -rf "$TOOLS/go"
      tar -C "$TOOLS" -xzf "$TOOLS/dl/$tarball"
    fi
    export PATH="$TOOLS/go/bin:$PATH"
  fi
  export GOPATH="$TOOLS/gopath" GOFLAGS=-modcacherw GOTOOLCHAIN=local

  echo "== landrun @ $LANDRUN_COMMIT"
  landrun_bin="$TOOLS/bin/landrun"
  if [ ! -x "$landrun_bin" ] || [ "$(cat "$landrun_bin.commit" 2>/dev/null)" != "$LANDRUN_COMMIT" ]; then
    GOBIN="$TOOLS/bin" CGO_ENABLED=0 go install "github.com/zouuup/landrun/cmd/landrun@$LANDRUN_COMMIT"
    echo "$LANDRUN_COMMIT" > "$landrun_bin.commit"
  fi

  echo "== lean4export @ $LEAN4EXPORT_COMMIT (tag v4.33.0), built with $toolchain"
  checkout_at https://github.com/leanprover/lean4export.git "$TOOLS/lean4export" "$LEAN4EXPORT_COMMIT"
  (cd "$TOOLS/lean4export" && lake "+$toolchain" build lean4export)

  echo "== comparator @ $COMPARATOR_COMMIT (tag v4.33.0), built with $toolchain"
  checkout_at https://github.com/leanprover/comparator.git "$TOOLS/comparator" "$COMPARATOR_COMMIT"
  (cd "$TOOLS/comparator" && lake "+$toolchain" build comparator)

  echo "== nanoda_lib @ $NANODA_COMMIT"
  checkout_at https://github.com/robsimmons/nanoda_lib.git "$TOOLS/nanoda" "$NANODA_COMMIT"
  cargo build --release --locked --quiet --manifest-path "$TOOLS/nanoda/Cargo.toml"

  for bin in "$TOOLS/comparator/.lake/build/bin/comparator" "$TOOLS/lean4export/.lake/build/bin/lean4export" \
      "$TOOLS/nanoda/target/release/nanoda_bin" "$landrun_bin"; do
    [ -x "$bin" ] || die "missing tool $bin"
  done
  echo "tools installed in $TOOLS"
}

run_comparator() {
  for bin in "$TOOLS/comparator/.lake/build/bin/comparator" "$TOOLS/lean4export/.lake/build/bin/lean4export" \
      "$TOOLS/nanoda/target/release/nanoda_bin" "$TOOLS/bin/landrun"; do
    [ -x "$bin" ] || die "missing tool $bin (run '$0 install' first)"
  done
  [ -f "$PROJECT/$CONFIG" ] || die "no $CONFIG in $PROJECT"
  python3 -c '
import json, sys
c = json.load(open(sys.argv[1]))
assert set(c["permitted_axioms"]) <= {"propext", "Quot.sound", "Classical.choice"}, "permitted_axioms"
assert c.get("enable_nanoda") is True, "enable_nanoda must be true"
' "$PROJECT/$CONFIG"

  if [ -n "${COMPARATOR_REUSE:-}" ]; then
    # a copy made by an earlier run (its sources are not refreshed)
    run="$COMPARATOR_REUSE"
    echo "== reusing the copy in $run"
  else
    run="$RUNS/$(date +%Y%m%d-%H%M%S)"
    echo "== fresh copy of the sources in $run"
    mkdir -p "$run"
    rsync -a --exclude=/.git --exclude=/.lake/build --exclude=/.cache \
      --exclude=/.lake/packages/ThreeSumApsp/3sum-apsp/.lake \
      --exclude=/.lake/packages/ThreeSumApsp/zeta23/.lake --exclude=__pycache__ \
      --exclude=/search/.venv --exclude=/papers/*/*.aux --exclude=/papers/*/*.log \
      "$PROJECT/" "$run/"
  fi
  cd "$run"
  # The compiled Mathlib (outside the sandbox: the sandbox has no network); a no-op if it was copied.
  lake exe cache get >/dev/null
  # Optionally compile the dependencies and the library first, on a bounded set of CPUs (this
  # version of Lake has no option for the number of jobs, and the sandboxed build would use every
  # core); Comparator then finds them built and checks them.
  if [ -n "${COMPARATOR_CPUS:-}" ]; then
    echo "== taskset -c $COMPARATOR_CPUS lake build ImprovedExponents (outside the sandbox)"
    taskset -c "$COMPARATOR_CPUS" lake build ImprovedExponents >/dev/null
  fi

  # Comparator runs `lake build <module>` and lean4export inside sandboxes that may execute only the
  # toolchain directory, so resolve lake/lean to the toolchain's own binaries rather than the elan shims.
  lean_prefix="$(lean --print-prefix)"
  export PATH="$lean_prefix/bin:$PATH"
  export COMPARATOR_LANDRUN="$TOOLS/bin/landrun"
  export COMPARATOR_LEAN4EXPORT="$TOOLS/lean4export/.lake/build/bin/lean4export"
  export COMPARATOR_NANODA="$TOOLS/nanoda/target/release/nanoda_bin"
  export LEAN_ABORT_ON_PANIC=1

  log="$run/comparator.log"
  {
    echo "project copy: $run"
    echo "toolchain: $(cat lean-toolchain)"
    echo "comparator $COMPARATOR_COMMIT, lean4export $LEAN4EXPORT_COMMIT, nanoda $NANODA_COMMIT, landrun $LANDRUN_COMMIT"
    echo "config: $CONFIG"
    cat "$CONFIG"
    echo "started: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  } > "$log"
  echo "== comparator $CONFIG (log: $log)"
  set +e
  lake env "$TOOLS/comparator/.lake/build/bin/comparator" "$CONFIG" 2>&1 | tee -a "$log"
  status="${PIPESTATUS[0]}"
  set -e
  echo "finished: $(date -u +%Y-%m-%dT%H:%M:%SZ), exit status $status" >> "$log"
  if [ "$status" -eq 0 ] && grep -qxF 'Your solution is okay!' "$log"; then
    echo "PASS $CONFIG"
  else
    die "comparator did not accept $CONFIG (exit status $status)"
  fi
}

case "${1:-}" in
  install) install_tools ;;
  run) run_comparator ;;
  all) install_tools; run_comparator ;;
  *) echo "usage: $0 install|run|all" >&2; exit 2 ;;
esac
