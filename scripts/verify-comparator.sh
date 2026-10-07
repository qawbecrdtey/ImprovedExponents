#!/usr/bin/env bash
# Judge ImprovedSolution against ImprovedChallenge the way the Palomar registry does: with the
# `lake comparator` that ships in a toolchain of version v4.35.0-rc2 or later. THIS PROJECT IS AT
# v4.33.1, where Comparator is a standalone tool: use scripts/comparator.sh instead. This script is
# kept for the day the toolchain is upgraded (README.md, "The registry's toolchain floor"). It rebuilds both modules in a bubblewrap sandbox, exports them, checks that every
# theorem named in comparator.json has the same statement on both sides and uses no axiom outside
# the permitted list, and replays the solution through Lean's kernel and the toolchain's bundled
# independent kernels NanoDa and con-ron. Adapted from PalomarRegistry/PalomarTemplate,
# scripts/verify-comparator.sh.
#
#     scripts/verify-comparator.sh                 # from anywhere; needs bwrap on the PATH
#     scripts/verify-comparator.sh --paranoid      # also leanchecker-paranoid, lean4lean, con-leche
#
# Palomar ignores `enable_nanoda` and rejects `external_kernels` in a submitted comparator.json: it
# registers the toolchain's bundled kernels itself. This script does the same in a generated copy of
# the configuration, so that the local check judges as the registry does. Nothing here is a
# verifier pin: everything that judges comes from lean-toolchain.
set -euo pipefail
project="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project"

for required in bwrap lake lean python3; do
  command -v "$required" >/dev/null 2>&1 || { echo "error: $required is required (bwrap: see scripts/install-bwrap.sh)" >&2; exit 1; }
done
toolchain="$(tr -d '[:space:]' < lean-toolchain)"
prefix="$(lean --print-prefix)"
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  [ -x "$prefix/bin/$tool" ] || { echo "error: toolchain $toolchain does not bundle $tool; Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2; exit 1; }
done

config="$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")"
trap 'rm -f "$config"' EXIT
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

lake exe cache get
echo "== lake comparator --config comparator.json (toolchain $toolchain) $*"
lake comparator --config "$config" "$@"
