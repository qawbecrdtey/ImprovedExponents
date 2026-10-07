# ImprovedExponents

A Lean 4 formalization of improved running-time exponents for 3SUM, Exact Triangle, the
(min,+)-product and all-pairs shortest paths (APSP), with the accompanying paper *Improved
exponents for 3SUM and APSP from triangles in sparse lopsided graphs*
(`papers/improved-exponents/`). It builds on the formalization by Anthropic of the paper of Josh
Alman and Virginia Vassilevska Williams, *Truly Subquadratic 3SUM and Truly Subcubic APSP via
Triangles in Sparse Lopsided Graphs* ([arXiv:2610.06783](https://arxiv.org/abs/2610.06783)), which
is [`anthropics/formal-math/3sum-apsp`](https://github.com/anthropics/formal-math/tree/main/3sum-apsp)
("upstream"). The part of upstream that this project uses is included in `upstream/3sum-apsp/`, at a
pinned commit, and ported from Lean `v4.33.1` to `v4.35.0-rc2` with four files changed
(`upstream/README.md`).

Repository: <https://github.com/qawbecrdtey/ImprovedExponents>. The repository is laid out for the
[Palomar registry](https://palomar-registry.org/): the statement module `ImprovedChallenge.lean`,
the solution module `ImprovedSolution.lean`, the configuration `comparator.json` and the metadata
`formalization.yaml`.

**Who did what.** Every line of Lean, Python and LaTeX in this repository outside `upstream/` was
written by the language model Claude Fable 5.1 (Anthropic), run as an agent in Claude Code, under
the direction of Jihoon Hyun, who chose the paper and the goals, decided how the results are
stated, reviewed the outputs and wrote no Lean by hand. The move to Lean `v4.35.0-rc2` (the port of
`upstream/3sum-apsp/`, the renames that it required in `ImprovedExponents/`, and the scripts and
documents that changed with it) was made by Claude Opus 5.5 (Anthropic) in Claude Code, under the
same direction. `upstream/3sum-apsp/` is Anthropic's formalization, apart from the four changes
listed in `upstream/README.md`. The algorithms, the reductions and the whole framework are due to
Alman and Vassilevska Williams; see "The original work" below. `formalization.yaml` records the
same facts in the form that Palomar reads.

## What is proved

All statements are about programs of upstream's word RAM, in the sense of its `EndStatement.lean`:
`Q.SolvedInTime r` says that for every exponent `κ` there is a program that solves every instance
of `Q` with numbers of absolute value at most `n^κ` in `O(n^r)` steps, at every word size of at
least `b (⌊log₂ n⌋ + 1)` bits.

| Theorems | 3SUM | Exact Triangle | (min,+), APSP | (min,+), APSP, all-edges route | What is new |
|---|---|---|---|---|---|
| upstream (the paper's Theorem 22) | 1.9992 | 2.9983 | 2.99942 | — | — |
| `threeSum_paper`, … | 1.99908 | 2.99816 | 2.99939 | — | better parameters only |
| `threeSum_exact`, … | 1.99902 | 2.99804 | 2.99935 | — | exact count of the leaves |
| `threeSum_full`, …, `apsp_allEdges` | 1.99898 | 2.99795 | 2.99932 | 2.99795 | + reduction charged at the true middle size, + all-edges host |
| `threeSum_pruned`, …, `apsp_allEdges_pruned` | **1.99896** | **2.99791** | 2.99931 | **2.99791** | + pruned encodings |

None of the theorems has a hypothesis. They are in `ImprovedExponents/Statements.lean`; each row
also has `exactTriangle_…`, `minPlus_…` and `apsp_…`, and the all-edges route has `minPlus_allEdges`,
`apsp_allEdges` and `minPlus_allEdges_pruned`, `apsp_allEdges_pruned`. The general theorems behind
them, for all admissible parameters, are `allSolved_paper`, `allSolved_exact`, `allSolved_full`
(`ImprovedExponents/Pipeline/General.lean`) and `allSolved_pruned`
(`ImprovedExponents/Pipeline/PrunedClaim.lean`), and `minPlusSolved_full`, `minPlusSolved_pruned` in
`Statements.lean`; `allSolved_full_sup`, `allSolved_pruned_sup`, `minPlusSolved_full_sup`,
`minPlusSolved_pruned_sup` give every saving below the supremum of the method over the ratio.

**The three ingredients.**

1. *Exact count of the leaves.* The paper bounds the number of leaves of order at least `t` in a
   tile by a geometric series. `ImprovedExponents/ExactCount` bounds it by its true exponential rate,
   `∑_{d ≥ t} β_d ≤ (m+1)(L+1) M e^{m g₂(L/m, t/m)}`. The program is unchanged; its running time is
   re-derived with the new bound (`ImprovedExponents/Cost8X`). The same count gives Lemma 11 of the
   paper for every ratio `L/m ≥ 10` and every density of the wanted positions, with the split at
   the best order (`sum_card_Leaves_le_exp`).
2. *The reduction charged at the true size of the middle part.* In the reduction from Exact Triangle
   (Theorem 17 of the paper) an instance has only about `D/g` middle vertices, but the solver is
   called as if it had `D`. `ImprovedExponents/HostMid` re-verifies upstream's host with one added
   assignment, which passes the true size.
3. *Pruned encodings.* Only the leaves with at most `m` symbols `P₀` are ever read, and their
   encodings can be computed in `O(L M)` instead of `10^L` operations per band.
   `ImprovedExponents/PrunedEncoding` proves this as mathematics (the staged recursion, its
   correctness, its size, and the resulting costs of the method under the weaker thinness
   condition: `pruned_encoding`, `costsP`), and `ImprovedExponents/PrunedProgram` as a program:
   upstream's recursive encoder with a budget of symbols `P₀` (`encodePBody`; the dense slices are
   affordable since `7^L ≤ 9^{L-m} ≤ M`), the consumers of the encodings re-verified under the
   contract that only the leaves with at most `m` symbols `P₀` are right (`SegOn`), the cost
   analysis (`ImprovedExponents/Cost8P`), and the solver `programP`. The theorem `prunedEncoderClaim`
   (`ImprovedExponents/Pipeline/PrunedClaim.lean`) discharges what was once a hypothesis of the
   last row.

**The all-edges route to APSP** (footnote 10 of the paper). The known reductions give the
(min,+)-product and APSP a third of the saving of Exact Triangle. The host of Theorem 17 also solves
the all-edges version of Exact Triangle (for every pair of the two outer parts, whether it lies in a
zero triangle), by scanning each accepted pair only until its zero triangle is found
(`ImprovedExponents/AllEdges/Host`: at most `F(p) + n²` scans), and the (min,+)-product reduces to
the all-edges version on the same `n` vertices, with the comparison `x + y < u` expressed by `O(log)`
equalities (`ImprovedExponents/MinPlus`, `ImprovedExponents/AllEdges/Pairs`). Upstream's bit search
and repeated squaring finish the job. So APSP keeps the whole saving: `2.99795`, and `2.99791` with
pruned encodings.

**The optimum.** For a ratio `c = L/m` the saving of the method is exactly
`S(c) = R(Γ(c)) Γ(c)/2`, where `Γ(c)` is the value at which two explicit curves cross
(`isLUB_tupleSaving` in `ImprovedExponents/Optimum`). With the paper's encodings its supremum over
`c` lies in `(0.002059, 0.002061]`, and `S(c) ≥ 0.002059` only for `c ∈ (20.8, 22)`
(`optimum_global_full`); with pruned encodings it lies in `(0.002095, 0.002096]`, and
`S(c) ≥ 0.002095` only for `c ∈ (21, 23)` (`optimum_global`). The theorems reach every saving below
these suprema: upstream's thin-product program tests `D^18 ≤ N` before it runs its recursion, which
excludes the optimal ratio, and `ImprovedExponents/Pipeline/RegimeRS.lean` appends to the program a
test `D^r ≤ N^s` with a rational exponent (the analysis of the solver is done once for an abstract
regime test, of which both tests are instances). The paper's own accounting, which charges every
call at the nominal dimension, has the smaller supremum `F(Γ_{1/2}(c))` (`GamHalf`,
`isLUB_paperSaving`, `GamHalf_lt_Gam` in `ImprovedExponents/Optimum/PaperAccounting.lean`).

**Other identities.** The same saving formula, evaluated for an identity of Schönhage's form with
`s` outer outputs and inner length `b` (`shapeSaving s b c` in `ImprovedExponents/Optimum/Shapes`,
with `shapeSaving 9 4 c = S(c)`), has its supremum over `c` certified to `±10⁻⁶` for the nine other
shapes `(k, n)` with `s = kn`, `b = (k-1)(n-1)` of the paper's Table 2 (2253 cells); `shapes_table`
says that every one of them stays below `0.00188`, while `(3, 3)` exceeds `0.002095`. This is a
statement about the formula: the programs exist for `(3, 3)` only.

## The statement module, and what a reader must trust

`ImprovedChallenge.lean` is the module that Comparator and Palomar compare against the proofs. It
**imports nothing**, not even Mathlib. It contains, verbatim, the trusted file `EndStatement.lean`
of upstream (the word RAM, `Problem.SolvedInTime`, the four problems; 132 lines of Lean, Apache-2.0,
Anthropic), and then the four strongest theorems of the project, each with `sorry` in place of its
proof:

```lean
theorem threeSum_pruned : EndStatement.ThreeSum.SolvedInTime 1.99896
theorem exactTriangle_pruned : EndStatement.ExactTriangle.SolvedInTime 2.99791
theorem minPlus_allEdges_pruned : EndStatement.MinPlusProduct.SolvedInTime 2.99791
theorem apsp_allEdges_pruned : EndStatement.APSP.SolvedInTime 2.99791
```

`ImprovedSolution.lean` imports the theorems of the same names from the library and adds nothing;
`comparator.json` names the four. Comparator rebuilds both modules in a sandbox, checks that each
theorem has exactly the same statement on both sides (and every definition that the statements
mention, transitively), that the proofs use no axiom beyond `propext`, `Quot.sound` and
`Classical.choice` (so neither `sorry` nor `native_decide`), and replays the proofs in Lean's
kernel and in the independent kernels NanoDa and con-ron. `scripts/check-endstatement.sh` confirms
that the copy of `EndStatement.lean` is byte for byte `upstream/3sum-apsp/EndStatement.lean`, and
`scripts/check-upstream.sh` that this file is upstream's, unchanged.

So a reader who wants to believe the four theorems has to read `ImprovedChallenge.lean` (the
machine, the problems, what "solved in `O(n^r)` steps" means; upstream's `docs/MACHINE.md`,
[at the pinned commit](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/docs/MACHINE.md)
and not included here, explains the choices) and to trust Lean's kernel and the three standard
axioms. Nothing else: not Mathlib,
not upstream's proofs, not this library. The library proves the four theorems and much more; a
reader of the other theorems of `ImprovedExponents/Statements.lean` must also trust the definitions
they mention (Mathlib's reals and upstream's definitions). No file of the library contains `sorry`,
an axiom or `native_decide`; the numerical certificates are checked by the kernel (`norm_num`,
`decide`), not by compiled code.

## The original work

The algorithm that this project improves, the reductions, the thin-product framework with
Schönhage's identity and the all-edges idea of footnote 10 are the work of Josh Alman and Virginia
Vassilevska Williams, whose paper gave the first truly subquadratic deterministic algorithm for 3SUM
and the first truly subcubic one for APSP. This project changes their analysis and their algorithm in
the few places described above and proves what follows; everything else is theirs, and the reader is
referred to their paper for the ideas. The Lean formalization of their paper by Anthropic, which
proves its bounds on the same machine, made it possible to prove the improved bounds without
re-proving the paper: this project reuses its machine model, its programs and its lemmas, and adapts
some of its developments for parameters that upstream fixes (`NOTICE` lists the files). The authors
of the paper were not involved in this project and have not been asked to endorse it.

## How to check

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (`lean-toolchain`, `lakefile.toml`); upstream was
written for `v4.33.1`. Every Lean file uses the module system.

    lake exe cache get                        # Mathlib's compiled files
    lake build                                # upstream/3sum-apsp, the library, the statement module
                                              # (four deliberate `sorry` warnings), the solution module
    python3 scripts/check-lean-sources.py     # the registry's source requirements
    ruby scripts/validate-formalization.rb    # formalization.yaml
    scripts/check-upstream.sh                 # upstream/3sum-apsp is upstream's commit, every change
                                              # listed in upstream/README.md and marked, and exactly
                                              # the files that the project imports (network)
    scripts/check-endstatement.sh             # the copy of EndStatement.lean is verbatim
    python3 -m unittest discover -s search/tests -t .
    python3 -m search.certs --check           # the generated certificates match the generator
    make -C papers/improved-exponents         # the paper (pdflatex, bibtex)
    make -C papers/improved-exponents check   # every Lean name cited in the paper exists
    scripts/install-bwrap.sh .cache/bwrap     # bubblewrap, if it is not installed (no root)
    PATH="$PWD/.cache/bwrap:$PATH" scripts/verify-comparator.sh   # lake comparator, as Palomar runs
                                              # it, in a fresh copy (~/comparator-runs; about 10 GB)

`lake build --wfail ImprovedExponents ImprovedSolution` fails on any warning; the four `sorry`
warnings of `ImprovedChallenge` are deliberate. `.github/workflows/ci.yml` runs all of the above
except the paper.

**Comparator.** From Lean `v4.35.0-rc2` on, [Comparator](https://github.com/leanprover/comparator)
ships inside the toolchain as `lake comparator`, with the independent kernels NanoDa and con-ron;
the Palomar registry, which accepts only toolchains `v4.35.0-rc2` or later, judges submissions with
it. `scripts/verify-comparator.sh` runs it as the registry does, in a bubblewrap sandbox, and in a
fresh copy of the sources (the files tracked by git, with no build products, so that the challenge,
the solution and the whole library are compiled inside the sandbox; Mathlib comes from
`lake exe cache get`). On a host without `/run/user`, which the sandbox expects (OpenRC, some
containers), the script adds an empty one in a further namespace, or `sudo mkdir /run/user` does.
`lake comparator` accepted `comparator.json` on 2026-10-07 ("Your solution is okay!", with Lean's
kernel, NanoDa and con-ron); the log is `scripts/comparator-run.log`.

## Layout

| Path | Content |
|---|---|
| `ImprovedChallenge.lean`, `ImprovedSolution.lean`, `comparator.json` | the statement surface for Comparator and Palomar |
| `formalization.yaml` | the metadata of the formalization (provenance, authorship, automation, scope, review) |
| `ImprovedExponents/Statements.lean` | the theorems of the table |
| `ImprovedExponents/Pipeline/` | from the thin product to Exact Triangle and to the four problems, for arbitrary parameters |
| `ImprovedExponents/ExactCount/` | the exact count of the leaves |
| `ImprovedExponents/Cost8X/` | the running time of upstream's Section 4 program with the exact count |
| `ImprovedExponents/HostMid/` | the host of Theorem 17 that passes the true size of the middle part |
| `ImprovedExponents/ParamRoutines/` | routines for `⌊n^{a/b}⌋` and `⌈D^{c/d}⌉`, and the hosts at these parameters |
| `ImprovedExponents/Total/` | the exponent of Exact Triangle from the costs of the reduction |
| `ImprovedExponents/Optimum/` | the optimal parameters: closed form, certified values, the global bound; `Shapes/`: the saving formula for other identities, certified; `PaperAccounting.lean`: the supremum of the paper's own accounting |
| `ImprovedExponents/PrunedEncoding/` | pruned encodings, as mathematics |
| `ImprovedExponents/PrunedProgram/` | the pruned encoder as a program, the consumers of the encodings under the weaker contract, the solver `programP` |
| `ImprovedExponents/Cost8P/` | the running time of the solver with the pruned encoder |
| `ImprovedExponents/MinPlus/` | the (min,+)-product through all-edges Exact Triangle, as mathematics |
| `ImprovedExponents/AllEdges/` | the all-edges task and model, the all-edges host (`Host/`), the reduction from all pairs (`Pairs/`), and the chain to the (min,+)-product and APSP |
| `upstream/3sum-apsp/` | the part of upstream that the library imports, ported to `v4.35.0-rc2`; `upstream/README.md`: its source, what the port changed |
| `scripts/` | the checks above: source requirements, metadata, the copy of upstream, the verbatim copy, `lake comparator`, bubblewrap |
| `papers/improved-exponents/` | the accompanying paper (`main.pdf`), which states the results with their Lean names |
| `search/` | the numeric exploration (Python, standard library only), the generator of the certificates and notes |

## License

Apache License 2.0 (`LICENSE`). `upstream/3sum-apsp/` is part of upstream (Copyright (c) 2026
Anthropic, PBC), released under the same license, with its `LICENSE` and `NOTICE` beside it; the
files that the port changed carry a notice saying so. Parts of `ImprovedExponents/` are adapted from
upstream; `ImprovedChallenge.lean` contains upstream's `EndStatement.lean`; scripts come from the
Palomar starter template. See `NOTICE`.
