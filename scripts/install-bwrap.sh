#!/usr/bin/env bash
# Build bubblewrap 0.12.0, which `lake comparator` uses as its sandbox, from the upstream release
# tarball (checked against its SHA-256), without root, into the directory given as the argument.
# Adapted from PalomarRegistry/PalomarSubmission, scripts/install_bwrap.sh (MIT License), which is
# what the registry's verifier does. Needs curl, meson, ninja, a C compiler and libcap.
#
#     scripts/install-bwrap.sh .cache/bwrap     # then put .cache/bwrap on the PATH
set -euo pipefail
version=0.12.0
sha256=9760d007363e3abba7c747489910f9f82d9fca53ba3bd3282e396fa3c97a3314
prefix="${1:?usage: install-bwrap.sh <install-dir>}"
mkdir -p "$prefix"; prefix="$(cd "$prefix" && pwd -P)"
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
curl --fail --location --silent --show-error --proto '=https' --tlsv1.2 \
  --output "$work/bubblewrap.tar.xz" \
  "https://github.com/containers/bubblewrap/releases/download/v$version/bubblewrap-$version.tar.xz"
echo "$sha256  $work/bubblewrap.tar.xz" | sha256sum --check --quiet
tar -xJf "$work/bubblewrap.tar.xz" -C "$work"
(cd "$work/bubblewrap-$version" \
  && meson setup build -Dselinux=disabled -Dman=disabled -Dbash_completion=disabled \
       -Dzsh_completion=disabled -Dtests=false >/dev/null \
  && ninja -C build >/dev/null)
install -m 0755 "$work/bubblewrap-$version/build/bwrap" "$prefix/bwrap"
"$prefix/bwrap" --version
echo "$prefix/bwrap"
