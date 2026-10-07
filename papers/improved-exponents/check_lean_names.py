#!/usr/bin/env python3
"""Check that every Lean name cited in the paper exists.

Every `\\lean{...}` in `main.tex` and `sections/*.tex` must be

* a declaration of this project or of the upstream formalization (the last
  component of a dotted name is looked up, so `Claim.Theorem_17` is found as
  `Theorem_17`; of `Q.SolvedInTime r` only the first word is used), or
* a file or a directory of this project or of upstream.

Run from anywhere: `python3 papers/improved-exponents/check_lean_names.py`.
It exits with status 1 and lists the names that were not found.
"""
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OURS = ROOT / "ImprovedExponents"
UPSTREAM = ROOT / ".lake" / "packages" / "ThreeSumApsp" / "3sum-apsp"

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|"
    r"syntax|macro|elab)\s+([^\s:({\[]+)",
    re.M)


def declared(root: pathlib.Path) -> set[str]:
    names: set[str] = set()
    for path in root.rglob("*.lean"):
        if ".lake" in path.relative_to(root).parts:
            continue
        for name in DECL.findall(path.read_text(encoding="utf-8")):
            names.add(name)
            names.add(name.split(".")[-1])
    return names


def cited() -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for path in [HERE / "main.tex", *sorted((HERE / "sections").glob("*.tex"))]:
        text = "\n".join(line.split("%%")[0] for line in path.read_text().splitlines())
        for name in re.findall(r"\\lean\{([^}]*)\}", text):
            out.setdefault(name, []).append(path.name)
    return out


def is_path(name: str) -> bool:
    for base in (ROOT, OURS, UPSTREAM, UPSTREAM / "ThreeSumApsp"):
        if (base / name).exists():
            return True
    return False


def main() -> int:
    if not UPSTREAM.is_dir():
        print(f"upstream sources not found at {UPSTREAM}; run `lake update` first")
        return 1
    names = declared(OURS) | declared(UPSTREAM)
    refs = cited()
    missing = []
    for ref, files in sorted(refs.items()):
        head = ref.split()[0]
        if head in names or head.split(".")[-1] in names or is_path(head):
            continue
        missing.append((ref, sorted(set(files))))
    for ref, files in missing:
        print(f"NOT FOUND  {ref}   ({', '.join(files)})")
    print(f"{len(refs)} distinct Lean names cited, {len(missing)} not found")
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
