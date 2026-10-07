# Identity search for the thin-product theorem: notes

These notes cover Alman and Vassilevska Williams, arXiv 2610.06783 (the PDF is not part of the
repository; the notes were written against a local copy `../subquadratic_3sum.pdf`). Line numbers
`l.N` refer to the extracted text of the paper; re-create it with
`python3 -I -c "import pypdf,sys; ..."` (pypdf `extract_text` page by page).

All exponents are asymptotic. Polylogarithmic factors and the "for m large enough" conditions are
absorbed exactly as in the paper (Section 4.4), by giving up an arbitrarily small amount of every saving.

## The chain of exponents

A thin-product saving γ means: the wanted entries cost N²/D^γ when |W| ≤ N²/D^κ and D ≤ N^ε. It turns
into the following savings:

| problem | saving | where |
|---|---|---|
| Exact Triangle (ET) | γ·ε/2 | Theorem 17 with g = D^{γ/2}, Remark 20 |
| 3SUM | half of the ET saving | Theorem 21(a), 22 |
| APSP | a third of the ET saving | Theorem 21(b), 22 |
| APSP via all-edges ET | all of the ET saving | footnote 10, deterministic |
| 3SUM via [KPP16] | all of γ·ε | footnote 10, randomized; claimed, not re-derived |

The reduction fixes κ = 1/2, since its hash prime has p ≈ √D.

## Stage 0: baselines (`exponents.py`, `python3 -m search.exponents`)

Each row adds one lever to the row it is indented under. The parameters are optimized.

| lever | c | κ | γ | ε | ET | 3SUM | APSP | APSP fn10 |
|---|---|---|---|---|---|---|---|---|
| Thm 5 as stated | 19 | .5 | .0556 | .0556 | .001543 | 1.999228 | 2.999486 | 2.998457 |
| Cor 26 as stated | 21 | .5 | .0630 | .0556 | .001750 | 1.999125 | 2.999417 | 2.998250 |
| rounding slack: ε = R₂₁(γ) | 21 | .5 | .0653 | .0567 | .001850 | 1.999075 | 2.999383 | 2.998150 |
| Cor 32, best c | 22.22 | .5 | .0693 | .0535 | .001855 | 1.999073 | 2.999382 | 2.998145 |
| exact Lemma 11 (max–min), best c | 20.79 | .5 | .0688 | .0572 | .001968 | 1.999016 | 2.999344 | 2.998032 |
|   + pruned encodings | 21.27 | .5 | .0704 | .0568 | .002000 | 1.999000 | 2.999333 | 2.998000 |
|   + hash prime p = D^σ | 21.38 | .5185 | .0741 | .0556 | .002060 | 1.998970 | 2.999313 | 2.997940 |
|   + both | 21.92 | .5190 | .0759 | .0552 | .002095 | 1.998952 | 2.999302 | 2.997905 |

The best deterministic results with the paper's identity are 3SUM n^{1.998952} and APSP n^{2.997905}. The APSP
figure goes through footnote 10. The gate for Stages 1 and 3 is an ET saving ≥ 1.15 × 0.002095 ≈ 0.00241.

The regression tests reproduce the paper exactly:
- all 66 entries of Table 2, rounded down. A row's ε is the smallest R_c over the row's entries (l.2840);
- γ = ln(20/9)/(9 ln 4) and q = 0.4277… (Corollary 26);
- ε\* = ln 4/(5 ln 10);
- Theorem 22.

### Lever 1: rounding slack
Corollary 26 uses ε = 1/18, but with c = 21 its own bound allows ε = R₂₁(γ) ≈ 0.0567, where γ = 0.0653
balances γ = κ − q (Corollary 32).

### Lever 2: Lemma 11 taken exactly
The pruned recursion of Section 2 knows W in advance; Theorem 17 is non-adaptive (l.1843). The first
inequality of Lemma 11, |Leaves(U)| ≤ Σ_d min(|U|α_d, β_d), holds for every L ≥ 10m. Per m, relative
to M, the two bounds at order d = δm are:
- f1(δ) = −κ ln 4 + H(δ) + δ ln 9, which increases on [0, 0.9];
- g2(δ) = c·H((1−δ)/c) − c·H(1/c) + δ ln 9, which decreases for c > 10.

So the cost is M·e^{m·Γ} with Γ = f1(δ\*) = g2(δ\*) at their crossing, and γ = −Γ/ln 4. The sum over the
tiles is linear in |U| (l.1614). The finite sums with `math.comb` converge to this value
(`lemma11_finite_gamma`, m ≤ 800).

### Lever 3: pruned encodings (proved)
Only leaves with at most m symbols P0 contribute to an output string whose inner set has m levels. So
only those entries of the encoding are needed. Run Yates' algorithm level by level. Stage k holds
A_k[τ₁…τ_k, u_{k+1}…u_L] = Σ a[u] Π_{ℓ≤k} φ_{τℓ}(uℓ). The needed and possibly nonzero entries lie in
P_k × U_k, where:
- P_k = prefixes of terms with ≤ m symbols P0, of which there are Σ_{j≤m} C(k,j) 9^{k−j};
- U_k = suffixes of left variables with ≤ m inner variables, of which there are Σ_{i≤m} C(L−k,i) 4^i 3^{L−k−i}.

Entries outside this set are unneeded, or zero because a vanishes off inner sets of size m. Each needed
entry reads at most 3 parents, and those lie in P_{k−1} × U_{k−1} or are zero.

**Claim.** |P_k||U_k| ≤ (7/9)^{L−k} |P_L|, and |P_L| ≤ M/(1−ρ) with ρ = 9m/(L−m+1).

*Proof.*
1. Since C(k+1, j) ≥ C(k, j), we get |P_{k+1}| ≥ 9|P_k|.
2. Pascal's rule on C(L−k, i) gives |U_k| = 3|U_{k+1}| + 4·(the same sum restricted to i ≤ m−1) ≤ 7|U_{k+1}|.
   The constant 7 is the number of left variables.
3. Combining the two gives the factor 7/9 per stage.
4. The terms of |P_L| increase in j up to j = m, with consecutive ratio ≥ (L−m+1)/(9m) = 1/ρ. So the sum is
   at most M/(1−ρ). ∎

So a band costs O(L·M) operations instead of O(10^L). The encodings of all ≈ 4N/(√K·N0) bands then cost
O(L·N·√K·N0). Condition (10) becomes N ≥ √K·N0·D^γ, which gives
ε = ln 4 / (c·H(1/c)/2 + (c−1)·ln 3 + γ·ln 4) (`R_pruned`). The same argument works for the right encodings,
and for any identity in which the number of left (or right) variables is smaller than the number of terms
that feed outer outputs.

### Lever 4: size of the hash prime
Take p ∈ [D^σ/2, D^σ) in Theorem 17 instead of p ≈ √D. Then:
- **Pieces:** the middle part (piece × Z_p) has at most D vertices, so a piece has D^{1−σ}/g vertices.
- **Instances:** at most 2·D^σ chunks of ≤ n²/D^σ query pairs, so κ = σ. That makes 2ng·D^{2σ−1}
  instances. Building them costs n²g·D^{2σ}.
- **Choosing the prime:** n^ω·D^{3σ}. It is negligible.
- **Scans:** the prime-counting argument (l.1854–1900) works for every p and gives F(p) = O(νn³ log n/p),
  so the scans cost n³·D^{1−2σ}/g.

Balancing g gives n³·D^{−γ(σ)/2} whenever g = D^{1−2σ+γ/2} ≥ 1. So the best choice is the fixed point
σ = 1/2 + γ(σ)/4 ≈ 0.519, where γ(σ) is the saving at density κ = σ.

## Stage 2: what-if map (`family.py`, `python3 -m search.family`)

All rows use pruned encodings and the hash prime at its fixed point. Asymmetric shapes are used together with
their transposes, so tiles stay square.

| shape | s | b | best c | γ | ε | ET | 3SUM | APSP fn10 |
|---|---|---|---|---|---|---|---|---|
| **S(3,3)** | 9 | 4 | 21.92 | .0759 | .0552 | **.002095** | **1.998952** | **2.997905** |
| S(2,4) | 8 | 3 | 20.11 | .0749 | .0501 | .001876 | 1.999062 | 2.998124 |
| S(3,4) | 12 | 6 | 27.96 | .0746 | .0501 | .001868 | 1.999066 | 2.998132 |
| S(2,5) | 10 | 4 | 24.24 | .0742 | .0479 | .001777 | 1.999111 | 2.998223 |
| S(2,3) | 6 | 2 | 16.03 | .0742 | .0450 | .001670 | 1.999165 | 2.998330 |
| S(2,6) | 12 | 5 | 28.39 | .0733 | .0443 | .001624 | 1.999188 | 2.998376 |
| S(3,5) | 15 | 8 | 34.04 | .0732 | .0441 | .001614 | 1.999193 | 2.998386 |
| S(4,4) | 16 | 9 | 35.96 | .0729 | .0432 | .001574 | 1.999213 | 2.998426 |
| S(4,5) | 20 | 12 | 44.01 | .0714 | .0371 | .001324 | 1.999338 | 2.998676 |
| S(5,5) | 25 | 16 | 54.02 | .0698 | .0315 | .001099 | 1.999451 | 2.998901 |

- **Per-level mixtures.** Pairing S(3,3) with any other family member never helps: the optimizer drives the
  other shape's share to 0. γ hardly varies across the family (0.070–0.076), and S(3,3) also has the best ε. So
  mixing has no trade-off to exploit.
- **Per-regime choice.** Already inside every row: c, κ (= σ), D = n^ε and g are optimized jointly.
- **Hypothetical shapes** (s outer outputs, one term each, inner length b; `hypothetical()`). The table gives the
  best ET saving; * marks the gate, ≥ 0.002410.

  | s \ b | 3 | 4 | 5 | 6 | 8 |
  |---|---|---|---|---|---|
  | 5 | .003984\* | .005397\* | .006599\* | .007655\* | .009470\* |
  | 6 | .002963\* | .004003\* | .004883\* | .005654\* | .006971\* |
  | 7 | .002316 | .003121\* | .003801\* | .004393\* | .005403\* |
  | 8 | .001876 | .002523\* | .003067\* | .003541\* | .004345\* |
  | 9 | .001560 | .002095 | .002544\* | .002934\* | .003594\* |
  | 10 | .001325 | .001777 | .002156 | .002484\* | .003038\* |
  | 12 | .001003 | .001341 | .001624 | .001868 | .002280 |

**Gate: no shape in the proven class passes.**
- Every starred cell breaks the pairing bound b ≤ (k−1)(n−1) for s = kn:
  - s = 9 needs b ≥ 5 (the bound allows 4);
  - s = 8 = 2·4 needs b ≥ 4 (allows 3);
  - s = 6 = 2·3 needs b ≥ 3 (allows 2);
  - s = 5, 7 have no factorization with k, n ≥ 2.
- So Stages 1 and 3 are not triggered by Stage 2. An identity that matches one of these cells *in effect* would
  need a different sharing structure: outer outputs fed by several terms, or several inner outputs. Scoring such
  a shape first needs the generalized leaf counting of Stage 1, which is new mathematics.
- The ceiling such a shape would buy: the best realistic cells (s = 8–9, b = 4–5) give ET 0.0025–0.0031, i.e.
  3SUM ≈ 1.99845–1.99875.

## Stage 4: data-adaptive (killed as experiments; analytic conclusions)

### How much arrangement could matter at all
- **Lower bound.** In a tile, a leaf of order d is shared by at most C(L−m+d, d) output strings. So any wanted set
  U visits at least |U|·α_d/C(L−m+d, d) = |U|·β_d/M leaves of order d, and at least about |U| leaves in all. So the
  best case is γ → κ = 1/2.
- **Random U.** Each leaf of order d is visited with probability 1 − (1−|U|/M)^{C(L−m+d,d)}. The expectation is
  Σ_d β_d·(that probability) ≈ Σ_d min(|U|α_d, β_d), the max–min bound (γ ≈ 0.07). So random wanted sets behave
  like the worst case.
- **What a gain needs.** A cost near |U| needs U to be close to a union of sub-tiles (fixed outer variables at some
  levels). Arrangement can only help when W is far from random.

### E2: arrangement gain (calibrated, killed)
`experiments/e2_arrangement.py` counts |Leaves(U)| exactly for one tile at L=6, m=2, D=16, with density 1/4.
- Every case visits ≈ 70% of all 10^L leaves, with leaves/|U| ≈ 45–49:
  - random W;
  - separable W, w = f(a)+g(b), with identity, shuffled, or sorted arrangement;
  - Hankel W, w = F(a+b).
- The separable case is trivially easy by a different algorithm: each of its p bicliques is a full sub-product,
  so multiply it directly at about |W| total cost. Even so, the recursion shows no gain at this size.
- Feasible sizes have c = L/m ≈ 3, where the β_d grow instead of decaying, so every wanted set saturates the
  tree. The relevant regime (c ≈ 21) would need m ≥ 1, L ≥ 21, i.e. ≥ 10^21 leaves.
- Conclusion: simulation cannot probe arrangement effects. Killed.

### E1: zeros in the encodings from one-hot inputs (killed analytically)
- Consider a leaf with P0 at the level set Z. Its encoded value Φ_τ(a) is a ±1 sum over at least 3^{|Z|} rows
  of X, because φ_{P0} = −(x₁+x₂+x₃) leaves the row digit free.
- The leaves that dominate a query have order ≈ δ\*m ≈ 0.11m. So |Z| ≈ 0.89m, and the sum has ≥ 3^{0.89m}
  terms, each nonzero with probability ≈ 1/p = D^{−σ} = 4^{−0.52m}.
- The expected number of nonzero terms is then e^{0.26m} → ∞. So the zero fraction tends to 0, barring
  systematic cancellation. Killed.

### Remaining data-adaptive lead (not pursued)
- Gains need W far from random. The reductions from 3SUM (through Convolution-3SUM: [CH20], [VW13]) build Exact
  Triangle instances whose weights are array entries at additively combined indices.
- If one of the three edge sets has weights w(a,b) = F(a+b), then W_ϱ is a union of anti-diagonals. A
  3SUM-specific algorithm for Hankel-structured W might then beat the worst-case bound.
- This depends on details of those reductions that the paper does not reproduce, and it would only help 3SUM.

## Formalization (Lean, `../ImprovedExponents/`)

The improvement is formalized on top of the published formalization of the paper
(`anthropics/formal-math/3sum-apsp`, a Lake dependency). Statements are about programs of its word RAM.

| Theorem (`ImprovedExponents/Statements.lean`) | 3SUM | ET | (min,+), APSP | levers |
|---|---|---|---|---|
| `threeSum_paper`, … | 1.99908 | 2.99816 | 2.99939 | parameters only (levers 1 and "Cor 32, best c") |
| `threeSum_exact`, … | 1.99902 | 2.99804 | 2.99935 | + lever 2 |
| `threeSum_full`, … | 1.99898 | 2.99795 | 2.99932 | + lever 4 |
| `minPlus_allEdges`, `apsp_allEdges` | | | 2.99795 | + footnote 10 (all-edges route) |
| `threeSum_pruned`, … | 1.99896 | 2.99791 | 2.99931 | + lever 3 |
| `minPlus_allEdges_pruned`, `apsp_allEdges_pruned` | | | 2.99791 | + footnote 10 |

None of the theorems has a hypothesis (third round, below).

What changed relative to the notes above while formalizing:
- **Lever 2 is used in the Section 4 form.** The program is the paper's box algorithm (Theorem 30). The exact count
  enters as a bound on the tail Σ_{d≥t} β_d ≤ (m+1)(L+1)·M·e^{m·g₂(L/m, t/m)}, with
  g₂(c, δ) = ψ(c−1) − ψ(c−1+δ) − ψ(1−δ) + δ ln 9 and ψ(x) = x ln x. The proof compares integers; no entropy bounds.
- **Lever 4 is Theorem 17 in the paper's own parametrization.** Run it with D′ = D^{2σ} and g′ = D^{2σ−1}. Its
  instances have only ⌈⌊√D′⌋/g′⌉·⌊√D′⌋ ≈ D middle vertices; the paper charges the solver at D′. Passing the true
  size is one added assignment in the host program (`ImprovedExponents/HostMid`).
- **Closed form of the optimum per c.** With γ_Q(θ) = (2 − 4q(θ))/3 and Γ(c) the common value of γX(c, ·) and γ_Q at
  their crossing, the supremum of the savings over (θ, σ, ε) is R(Γ)·Γ/2; the optimal σ is 1/2 + Γ/4
  (`isLUB_tupleSaving`).
- **Global optimum.** With pruned encodings sup_c is in (0.002095, 0.002096] and is approached only for
  c ∈ (21, 23) (`optimum_global`; 222 certified cells generated by `certs.py`). With the paper's encodings
  sup_c is in (0.002059, 0.002061] and is approached only for c ∈ (20.8, 22) (`optimum_global_full`; 261 cells,
  `python3 -m search.certs --encoding full`).
- **The program's regime test.** The existing thin-product program tests D^18 ≤ N. This limits it to ratios with
  (c/2)H(1/c) + (c−1) ln 3 < 18 ln 4, i.e. c < 21.85, and to ε ≤ 1/18, which the optimum c ≈ 21.38 of the paper's
  encodings violates slightly (there 1/ε ≈ 17.98). `Pipeline/RegimeRS.lean` appends to upstream's program a test
  D^r ≤ N^s with natural r, s (`programRS`); the analysis of the solver is done once for an abstract regime
  (`RegimeTest`), of which both tests are instances. Any admissible ε admits a fraction r/s between
  A_pr(c)/ln 4 and 1/ε, so `allSolved_full` holds for every c ≥ 20 (the bound c ≥ 20 gives ε ≤ 1/16 for the
  Strassen term) and `allSolved_full_sup` for every saving below sup_c S_full(c). The numerals of
  `threeSum_paper`/`threeSum_exact` stay at c = 108/5 (existing program); those of `threeSum_full` are at c = 107/5.
- **Lever 3: mathematics and program.** `ImprovedExponents/PrunedEncoding` has the staged recursion, its
  correctness on the leaves with at most m symbols P0, at most (27/2)·M/(1−ρ) multiplications per band, and the
  costs of the method under ε < R′_c(γ) (`costsP`). The program (`ImprovedExponents/PrunedProgram`) is simpler
  than the staged recursion: upstream's recursive encoder with a budget of symbols P0 (the term with digit 9 is
  entered only while the budget lasts), with the dense slices of 7^{L−k} entries, which are affordable because
  7^L ≤ 9^{L−m} ≤ M for L ≥ 10m. Its work is Σ_k |P_k| 7^{L−k} ≤ (9/2)|P_L| ≤ (9/2) M/(1−ρ) (`encWorkP_le`,
  `tEncP_le`). The consumers of the encodings (upstream's Theorem 30 tile preprocessing and query) read a cell
  in exactly two places, both at leaves with at most m symbols P0, and are re-verified under the weaker contract
  `SegOn` (right at those leaves, arbitrary elsewhere; `fillListP_meets`, `queryAtP_of_base58`). The cost
  analysis is `ImprovedExponents/Cost8P` (`offlineWithinP`), the solver of all instances is generic in the offline
  routine (`OfflineRoutine`, `offline32PRoutine`), and `prunedEncoderClaim : PrunedEncoderClaim`
  (`Pipeline/PrunedClaim.lean`) discharges the former hypothesis; `programP G r s` is the solver.
- **Lever 2 in the Section 2 form** (Lemma 11 for all L ≥ 10m and every density of the wanted positions, split at
  the best order) is `sum_card_Leaves_le_exp` in `ImprovedExponents/ExactCount/Leaves.lean`; the theorems do not
  use it.
- **Footnote 10 is carried out as programs** (`ImprovedExponents/AllEdges`). Lemma F is `ImprovedExponents/MinPlus`;
  the host of Theorem 17 keeps n² flags and scans an accepted pair only while its flag is 0 (at most F(p) + n²
  scans, `sum_execsAE_le`; `ae17_solves`, `midHostRat_ae`), and a second host answers upstream's all-pairs
  threshold task with 2b + 3 all-edges instances (`isHost_pairsAE`); upstream's bit search and repeated squaring
  finish. The time model `lightModelAE` reads "Exact Triangle" as the all-edges task, so the deductions to
  `ExplicitFrom` are reused. Result: (min,+) and APSP in O(n^2.99795) (`apsp_allEdges`) and O(n^2.99791) with
  pruned encodings (`apsp_allEdges_pruned`), both without hypothesis.
- **The remaining paper-only statements** are formalized too: the strictness of Lemma 3.2(iv)
  (`gammaOf_lt_gammaX`), the remark of §6 on the paper's own accounting (`GamHalf`, `isLUB_paperSaving`,
  `GamHalf_lt_Gam`: its supremum is F(Γ_{1/2}(c)) < F(Γ(c))), and Table 2 of §9: the saving formula evaluated for
  a shape (s outer outputs, inner length b) is `shapeSaving s b c` (`Optimum/Shapes`, with
  `shapeSaving 9 4 c = savingF (basePruned c) (Gam c)`), and the supremum over c of each of the nine other shapes
  is enclosed to ±1e-6 (`sSup_shapeSaving_S24_mem`, …; 2253 cells, `python3 -m search.certs --encoding shapes`);
  `shapes_table` says every one of them stays below 0.00188 while S(3,3) exceeds 0.002095. Only the mixtures, the
  hypothetical grid and the experiments of §9 remain floating point.

## Results log
- Stage 0: done; tests in `tests/test_exponents.py`. Best: 3SUM 1.998952, APSP 2.997905 (footnote 10).
- Stage 2: done; tests in `tests/test_family.py`. Schönhage's S(3,3) is optimal in its class, and mixtures do
  not help. The gate is not passed.
- Stage 4: E1 and E2 killed (above). One analytic lead is recorded, not pursued.
- Stages 1 and 3: not started. They are gated on a decision to develop leaf counting for identities with a
  different sharing structure.
- Formalization: done (see the section above). The accompanying paper is `../papers/improved-exponents/`.
- Second round (2026-10-07): the regime test with a rational exponent (the unconditional theorem reaches the
  optimum of the paper's encodings), the certified optimum with the paper's encodings, footnote 10 as programs
  (APSP 2.99795 unconditional), and Comparator run through `../scripts/comparator.sh` (tools at the revisions of
  upstream's CI; "Your solution is okay!" with both kernels).
- Third round (2026-10-07): the pruned encoder as a program and the proof of `PrunedEncoderClaim` (every
  theorem is now unconditional: 3SUM 1.99896, ET and APSP 2.99791), the strictness of Lemma 3.2(iv), the §6
  remark, and the certified Table 2 of the shapes. Comparator rerun on the four strongest statements.
- Palomar round (2026-10-07): the project renamed `ImprovedExponents`, every Lean file ported to the module
  system, the statement module `../ImprovedChallenge.lean` made import-free by inlining upstream's
  `EndStatement.lean`, Comparator rerun with the standalone tools (`../scripts/comparator.sh`), and
  `../formalization.yaml` and `../README.md` written for the registry. The toolchain stays at `v4.33.1` by
  decision of the maintainer; the registry's floor is `v4.35.0-rc2`, where Comparator ships as
  `lake comparator` (`../scripts/verify-comparator.sh` is for that day).
