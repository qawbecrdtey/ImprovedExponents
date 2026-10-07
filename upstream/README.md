# upstream/3sum-apsp: part of Anthropic's formalization, ported to Lean v4.35.0-rc2

The directory `3sum-apsp/` holds part of the Lean 4 formalization of the paper *Truly Subquadratic
3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs* by Josh Alman and Virginia
Vassilevska Williams (arXiv:2610.06783), taken from

    https://github.com/anthropics/formal-math, directory 3sum-apsp,
    commit e1a4e6508154ea59f030480661590a9fe3018011

Copyright (c) 2026 Anthropic, PBC, released under the Apache License, Version 2.0. Its licence and its
notice are `3sum-apsp/LICENSE` and `3sum-apsp/NOTICE`, both unchanged; the notice is also reproduced
in the `NOTICE` of this repository. This file is not part of upstream.

**Why it is here.** Upstream is a research artifact, not maintained, and pinned to Lean and Mathlib
`v4.33.1`. The Palomar registry accepts only toolchains `v4.35.0-rc2` or later, so this project cannot
depend on upstream through Lake; instead it includes the part of upstream that it uses, ported to
Lean and Mathlib `v4.35.0-rc2`.

**What is included.** Exactly the 340 files of Lean that the library `ImprovedExponents` imports,
directly or transitively: `EndStatement.lean` (the trusted statements, copied verbatim into
`ImprovedChallenge.lean`), `PaperStatements.lean` and 338 files of `ThreeSumApsp/`, at the same paths
as upstream, with the same module names. Left out: upstream's other 94 files of Lean, which nothing
here imports (the umbrella `ThreeSumApsp.lean`, `Challenge/`, `Solution/`, `scripts/PrintAxioms.lean`,
and 88 files of `ThreeSumApsp/`, among them the umbrella files of its directories, most of Section 5,
the conditional times and the model checks), and its documentation, scripts and build files. `lakefile.toml` builds the included files as upstream's three
libraries `EndStatement`, `PaperStatements` and `ThreeSumApsp`, with upstream's options.

**What the port changes.** Only what no longer compiles with Lean and Mathlib `v4.35.0-rc2`, and no
statement and no definition. The deprecation warnings of the new versions (for example core's
`if_pos`, now `ite_eq_left`) are switched off for these three libraries in `lakefile.toml` rather
than fixed, so that every other file stays upstream's, byte for byte. Each changed file has, in its
header after upstream's copyright and licence lines, the line

    Modified in 2026 for ImprovedExponents (Jihoon Hyun): ported to Lean and Mathlib v4.35.0-rc2.

The changed files are listed below (paths relative to `3sum-apsp/`); `scripts/check-upstream.sh`
reads this list.

<!-- changed files: begin -->
- `ThreeSumApsp/Sec2/Theorem5.lean`: in `sum_card_wantedStrings_le`, `congr 1` now closes the goal,
  so the two tactics after it are removed.
- `ThreeSumApsp/Sec3/Theorem17/Hashing.lean`: Mathlib's `Finset.prod_le_prod` (with a hypothesis of
  nonnegativity) is now `Finset.prod_le_prod₀`.
- `ThreeSumApsp/Util/Asymptotics/Scale.lean`: the same rename, twice.
- `ThreeSumApsp/Util/Sum.lean`: Mathlib's `Finset.prod_le_one` (with a hypothesis of nonnegativity)
  is now `Finset.prod_le_one₀`.
<!-- changed files: end -->

**How to check.**

    scripts/check-upstream.sh       # fetches upstream at the commit above and compares every file
    git diff 3a5a334 -- upstream/   # the port, against the unmodified import of the files

`scripts/check-upstream.sh` confirms that every file of `3sum-apsp/` is upstream's file of the same
path, identical to it or listed above and marked, that every listed file differs from upstream, and
that `LICENSE`, `NOTICE` and `EndStatement.lean` are identical to upstream's. The commit `3a5a334` of
this repository added the files exactly as upstream has them.
