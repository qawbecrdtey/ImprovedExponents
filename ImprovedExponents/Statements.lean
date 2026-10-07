module

public import ThreeSumApsp.Statements.Exponents
public import ImprovedExponents.Pipeline.General
public import ImprovedExponents.Pipeline.PrunedClaim
public import ImprovedExponents.Optimum.NumValues
public import ImprovedExponents.Optimum.NumWitness
public import ImprovedExponents.Optimum.Global
public import ImprovedExponents.Optimum.GlobalFull
public import ImprovedExponents.AllEdges.Pairs.TimeBound
public import ImprovedExponents.AllEdges.Host.ClaimAE

@[expose] public section

/-!
# The improved bounds for 3SUM, Exact Triangle, the (min,+)-product and APSP

The statements of this file are about programs of the word RAM of upstream's `EndStatement.lean`:
`Q.SolvedInTime r` says that for every exponent `κ` there are a program, a slope `b` and a time
bound `T(n) = O(n^r)` such that the program solves every instance of `Q` whose numbers have
absolute value at most `n^κ`, at every word size of at least `b (⌊log₂ n⌋ + 1)` bits, within `T(n)`
steps. Upstream proves the paper's Theorem 22 in this form: 3SUM with `r = 1.9992`, the
(min,+)-product and APSP with `r = 2.99942`, Exact Triangle with `r = 3 - 0.0017`.

Four sets of bounds follow, in the order of the ingredients they use. `δ` is the saving for Exact
Triangle; 3SUM keeps half of it and the (min,+)-product and APSP a third, or all of it through
all-edges Exact Triangle (`…_allEdges`). None of them has a hypothesis.

| | ingredients | `δ >` | 3SUM | Exact Triangle | (min,+), APSP | all-edges route |
|---|---|---|---|---|---|---|
| `…_paper` | the paper's algorithm and analysis, better parameters | 0.00184 | 1.99908 | 2.99816 |
2.99939 | |
| `…_exact` | + exact count of the leaves | 0.00196 | 1.99902 | 2.99804 | 2.99935 | |
| `…_full` | + reduction charged at the true middle size | 0.002059 | 1.99898 | 2.99795 | 2.99932 |
2.99795 |
| `…_pruned` | + pruned encodings | 0.002095 | 1.99896 | 2.99791 | 2.99931 | 2.99791 |

The numerals of the first two rows are taken at the ratio `c = 108/5`, which the regime test
`D^18 ≤ N` of the existing program admits; those of the third at `c = 107/5`, near the optimum of
the method, with the solver whose test is `D^r ≤ N^s` (`ImprovedExponents.Pipeline.RegimeRS`); those
of the last at `c = 22`, with the solver whose encoder is pruned
(`ImprovedExponents.PrunedProgram`, `ImprovedExponents.Pipeline.PrunedClaim`). The general theorems
behind them are `allSolved_paper`, `allSolved_exact`, `allSolved_full`
(`ImprovedExponents.Pipeline.General`) and `allSolved_pruned`
(`ImprovedExponents.Pipeline.PrunedClaim`), and the optima over the ratio are
`optimum_global_full` (paper's encodings) and `optimum_global` (pruned encodings);
`allSolved_full_sup` and `allSolved_pruned_sup` give every saving below them.
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.WordRam Light Real

/-! ## From a saving to the end statements -/

/-- The four end statements at rational exponents above the bounds of a saving `δ`. -/
theorem AllSolved.endStatements {δ : ℝ} (h : AllSolved δ) {r₃ rE rM : ℚ}
    (h₃ : 2 - δ / 2 < (r₃ : ℝ)) (hE : 3 - δ < (rE : ℝ)) (hM : 3 - δ / 3 < (rM : ℝ))
    (h₃0 : 0 ≤ r₃) (hE0 : 0 ≤ rE) (hM0 : 0 ≤ rM) :
    EndStatement.ThreeSum.SolvedInTime r₃ ∧ EndStatement.ExactTriangle.SolvedInTime rE ∧
      EndStatement.MinPlusProduct.SolvedInTime rM ∧ EndStatement.APSP.SolvedInTime rM :=
  ⟨SolvedInTime.endStatement (h.threeSum _ h₃) rfl h₃0,
    SolvedInTime.endStatement (h.exactTriangle _ hE) rfl hE0,
    SolvedInTime.endStatement (h.minPlus _ hM) rfl hM0,
    SolvedInTime.endStatement (h.apsp _ hM) rfl hM0⟩

/-! ## The savings -/

/-- The tile fits in the regime of the program's test at the ratio `c = 108/5`. -/
theorem basePruned_108_5_lt : basePruned (108 / 5) < 18 * log 4 :=
  lt_of_le_of_lt (basePruned_monotoneOn (Set.mem_Ici.2 (by norm_num)) (Set.mem_Ici.2 (by norm_num))
    (by norm_num)) basePruned_lt_18

/-- **The paper's algorithm and analysis at better parameters** (`c = 108/5`, `κ = 1/2`): a saving
of more than `0.00184` for Exact Triangle (the paper has `0.00175`). -/
theorem allSolved_paper_num : ∃ δ : ℝ, (0.00184 : ℝ) < δ ∧ AllSolved δ := by
  obtain ⟨θ, γ, γ', ε, hθ0, hθ1, hγ0, hγle, hγ'ge, hq, hε0, hε, hnum⟩ := t2_witness
  have hθ0' : (0 : ℚ) < θ := by exact_mod_cast hθ0
  have hθ_eq := rat_eq_div hθ0'.le
  have hgam0 : 0 ≤ gammaOf (108 / 5) θ := hγ0.le.trans hγle
  have hR : (ε : ℝ) < Rc (108 / 5) (gammaOf (108 / 5) θ) :=
    hε.trans_le ((Rc_strictAntiOn_right _ (by norm_num)).antitoneOn (Set.mem_Ici.2 hgam0)
      (Set.mem_Ici.2 (hgam0.trans hγ'ge)) hγ'ge)
  have hR18 : Rc (108 / 5) (gammaOf (108 / 5) θ) ≤ 1 / 18 := by
    rw [Rc_eq_thinR]
    exact thinR_le_inv (by norm_num) baseFull_ge_18 hgam0
  have hq0 : 0 ≤ qOf θ := qOf_nonneg θ hθ0 (by norm_num; linarith)
  have hmin : (γ : ℝ) / 2 ≤ min (gammaOf (108 / 5) θ) (1 / 2 - qOf θ) - γ / 2 := by
    have := le_min hγle (by linarith : (γ : ℝ) ≤ 1 / 2 - qOf θ)
    linarith
  have hc : ((108 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 108 / 5 := by norm_num
  refine ⟨(0.00184 + ε * (γ / 2)) / 2, by linarith, ?_⟩
  refine allSolved_paper (a := 108) (b := 5) (p := θ.num.toNat) (q := θ.den) (by norm_num)
    θ.den_pos (by norm_num) (one_le_num_toNat hθ0')
    (mul_num_lt_mul_den hθ0'.le (by norm_num) (by exact_mod_cast hθ1))
    (by rw [hc]; exact basePruned_108_5_lt)
    (ε := (ε + Rc (108 / 5) (gammaOf (108 / 5) θ)) / 2) (by rw [hc, ← hθ_eq]; linarith)
    (by linarith) (d := ε) (η := γ / 2) (by exact_mod_cast hε0) (by linarith)
    (by have : (0 : ℚ) < γ := by exact_mod_cast hγ0
        positivity)
    (by push_cast; linarith) (by positivity) ?_
  rw [hc, ← hθ_eq]
  push_cast
  rw [min_eq_left hmin]
  linarith

/-- **With the exact count of the leaves** (`c = 108/5`, `κ = 1/2`): a saving of more than
`0.00196` for Exact Triangle. -/
theorem allSolved_exact_num : ∃ δ : ℝ, (0.00196 : ℝ) < δ ∧ AllSolved δ := by
  obtain ⟨θ, γ, ε, hθ0, hθ1, hγ0, hγlt, hq, hε0, hε, hnum⟩ := t3_witness
  have hθ0' : (0 : ℚ) < θ := by exact_mod_cast hθ0
  have hθ_eq := rat_eq_div hθ0'.le
  have hR18 : Rc (108 / 5) γ ≤ 1 / 18 := by
    rw [Rc_eq_thinR]
    exact thinR_le_inv (by norm_num) baseFull_ge_18 hγ0.le
  have hq0 : 0 ≤ qOf θ := qOf_nonneg θ hθ0 (by norm_num; linarith)
  have hmin : (γ : ℝ) / 2 ≤ min (γ : ℝ) (1 / 2 - qOf θ) - γ / 2 := by
    rw [min_eq_left (by linarith)]
    linarith
  have hc : ((108 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 108 / 5 := by norm_num
  refine ⟨(0.00196 + ε * (γ / 2)) / 2, by linarith, ?_⟩
  refine allSolved_exact (a := 108) (b := 5) (p := θ.num.toNat) (q := θ.den) (by norm_num)
    θ.den_pos (by norm_num) (one_le_num_toNat hθ0')
    (mul_num_lt_mul_den hθ0'.le (by norm_num) (by exact_mod_cast hθ1))
    (by rw [hc]; exact basePruned_108_5_lt) (γ := γ) hγ0 (by rw [hc, ← hθ_eq]; exact hγlt)
    (ε := (ε + Rc (108 / 5) γ) / 2) (by rw [hc]; linarith)
    (by linarith) (d := ε) (η := γ / 2) (by exact_mod_cast hε0) (by linarith)
    (by have : (0 : ℚ) < γ := by exact_mod_cast hγ0
        positivity)
    (by push_cast; linarith) (by positivity) ?_
  rw [← hθ_eq]
  push_cast
  rw [min_eq_left hmin]
  linarith

/-- **With the reduction charged at the true size of the middle part** (`c = 107/5`, with the
regime test `D^r ≤ N^s` of `ImprovedExponents.Pipeline.RegimeRS`): a saving of more than `0.002059`
for Exact Triangle; every saving below `R_c(Γ) Γ/2 = 0.0020599…`. -/
theorem allSolved_full_num : ∃ δ : ℝ, (0.002059 : ℝ) < δ ∧ AllSolved δ :=
  ⟨(0.002059 + savingF (baseFull (107 / 5)) (Gam (107 / 5))) / 2,
    by linarith [savingF_full_107_5_gt],
    allSolved_full (by norm_num : (20 : ℝ) ≤ 107 / 5)
      (by linarith [savingF_full_107_5_gt]) (by linarith [savingF_full_107_5_gt])⟩

/-- **With pruned encodings** (`c = 22`): a saving of more than `0.002095` for Exact Triangle;
every saving below `R'_c(Γ) Γ/2 = 0.0020952…`. -/
theorem allSolved_pruned_num :
    ∃ δ : ℝ, (0.002095 : ℝ) < δ ∧ AllSolved δ :=
  ⟨(0.002095 + savingF (basePruned 22) (Gam 22)) / 2, by linarith [savingF_pruned_gt],
    allSolved_pruned (c := 22) (by norm_num) (by linarith [savingF_pruned_gt])
      (by linarith [savingF_pruned_gt])⟩

/-! ## The paper's algorithm and analysis at better parameters -/

/-- 3SUM in `O(n^1.99908)`, Exact Triangle in `O(n^2.99816)`, the (min,+)-product and APSP in
`O(n^2.99939)`: the paper's algorithm with the paper's analysis, at better parameters. -/
theorem endStatements_paper :
    EndStatement.ThreeSum.SolvedInTime 1.99908 ∧
      EndStatement.ExactTriangle.SolvedInTime 2.99816 ∧
      EndStatement.MinPlusProduct.SolvedInTime 2.99939 ∧
      EndStatement.APSP.SolvedInTime 2.99939 := by
  obtain ⟨δ, hδ, h⟩ := allSolved_paper_num
  exact h.endStatements (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num) (by norm_num) (by norm_num)

/-- 3SUM in `O(n^1.99908)` steps on the word RAM, with the paper's algorithm and analysis. -/
theorem threeSum_paper : EndStatement.ThreeSum.SolvedInTime 1.99908 := endStatements_paper.1

/-- Exact Triangle in `O(n^2.99816)` steps on the word RAM: the paper's algorithm and analysis. -/
theorem exactTriangle_paper : EndStatement.ExactTriangle.SolvedInTime 2.99816 :=
  (endStatements_paper).2.1

/-- The (min,+)-product in `O(n^2.99939)` steps on the word RAM: the paper's algorithm and
analysis. -/
theorem minPlus_paper : EndStatement.MinPlusProduct.SolvedInTime 2.99939 :=
  (endStatements_paper).2.2.1

/-- APSP in `O(n^2.99939)` steps on the word RAM: the paper's algorithm and analysis. -/
theorem apsp_paper : EndStatement.APSP.SolvedInTime 2.99939 :=
  (endStatements_paper).2.2.2

/-! ## With the exact count of the leaves -/

/-- 3SUM in `O(n^1.99902)`, Exact Triangle in `O(n^2.99804)`, the (min,+)-product and APSP in
`O(n^2.99935)`: the paper's algorithm, with the exact count of the leaves. -/
theorem endStatements_exact :
    EndStatement.ThreeSum.SolvedInTime 1.99902 ∧
      EndStatement.ExactTriangle.SolvedInTime 2.99804 ∧
      EndStatement.MinPlusProduct.SolvedInTime 2.99935 ∧
      EndStatement.APSP.SolvedInTime 2.99935 := by
  obtain ⟨δ, hδ, h⟩ := allSolved_exact_num
  exact h.endStatements (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num) (by norm_num) (by norm_num)

/-- 3SUM in `O(n^1.99902)` steps on the word RAM, with the exact count of the leaves. -/
theorem threeSum_exact : EndStatement.ThreeSum.SolvedInTime 1.99902 := endStatements_exact.1

/-- Exact Triangle in `O(n^2.99804)` steps on the word RAM: with the exact count of the leaves. -/
theorem exactTriangle_exact : EndStatement.ExactTriangle.SolvedInTime 2.99804 :=
  (endStatements_exact).2.1

/-- The (min,+)-product in `O(n^2.99935)` steps on the word RAM: with the exact count of the
leaves. -/
theorem minPlus_exact : EndStatement.MinPlusProduct.SolvedInTime 2.99935 :=
  (endStatements_exact).2.2.1

/-- APSP in `O(n^2.99935)` steps on the word RAM: with the exact count of the leaves. -/
theorem apsp_exact : EndStatement.APSP.SolvedInTime 2.99935 :=
  (endStatements_exact).2.2.2

/-! ## With the reduction charged at the true size of the middle part -/

/-- 3SUM in `O(n^1.99898)`, Exact Triangle in `O(n^2.99795)`, the (min,+)-product and APSP in
`O(n^2.99932)`: the exact count and the reduction that passes the true size of the middle part. -/
theorem endStatements_full :
    EndStatement.ThreeSum.SolvedInTime 1.99898 ∧
      EndStatement.ExactTriangle.SolvedInTime 2.99795 ∧
      EndStatement.MinPlusProduct.SolvedInTime 2.99932 ∧
      EndStatement.APSP.SolvedInTime 2.99932 := by
  obtain ⟨δ, hδ, h⟩ := allSolved_full_num
  exact h.endStatements (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num) (by norm_num) (by norm_num)

/-- **3SUM in `O(n^1.99898)` steps on the word RAM.** No hypothesis. -/
theorem threeSum_full : EndStatement.ThreeSum.SolvedInTime 1.99898 := endStatements_full.1

/-- Exact Triangle in `O(n^2.99795)` steps on the word RAM: the exact count and the true
middle size. -/
theorem exactTriangle_full : EndStatement.ExactTriangle.SolvedInTime 2.99795 :=
  (endStatements_full).2.1

/-- The (min,+)-product in `O(n^2.99932)` steps on the word RAM: the exact count and the true
middle size. -/
theorem minPlus_full : EndStatement.MinPlusProduct.SolvedInTime 2.99932 :=
  (endStatements_full).2.2.1

/-- APSP in `O(n^2.99932)` steps on the word RAM: the exact count and the true middle size. -/
theorem apsp_full : EndStatement.APSP.SolvedInTime 2.99932 :=
  (endStatements_full).2.2.2

/-! ## With pruned encodings -/

/-- With pruned encodings: 3SUM in `O(n^1.99896)`, Exact Triangle in `O(n^2.99791)`, the
(min,+)-product and APSP in `O(n^2.99931)`. -/
theorem endStatements_pruned :
    EndStatement.ThreeSum.SolvedInTime 1.99896 ∧
      EndStatement.ExactTriangle.SolvedInTime 2.99791 ∧
      EndStatement.MinPlusProduct.SolvedInTime 2.99931 ∧
      EndStatement.APSP.SolvedInTime 2.99931 := by
  obtain ⟨δ, hδ, h⟩ := allSolved_pruned_num
  exact h.endStatements (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num) (by norm_num) (by norm_num)

/-- **3SUM in `O(n^1.99896)` steps on the word RAM**: the exact count, the true middle size and
pruned encodings. No hypothesis. -/
theorem threeSum_pruned : EndStatement.ThreeSum.SolvedInTime 1.99896 :=
  endStatements_pruned.1

/-- **Exact Triangle in `O(n^2.99791)` steps on the word RAM**, with pruned encodings. No
hypothesis. -/
theorem exactTriangle_pruned : EndStatement.ExactTriangle.SolvedInTime 2.99791 :=
  endStatements_pruned.2.1

/-- The (min,+)-product in `O(n^2.99931)` steps on the word RAM, with pruned encodings and a third
of the saving (see `minPlus_allEdges_pruned` for the whole saving). -/
theorem minPlus_pruned : EndStatement.MinPlusProduct.SolvedInTime 2.99931 :=
  endStatements_pruned.2.2.1

/-- APSP in `O(n^2.99931)` steps on the word RAM, with pruned encodings and a third of the saving
(see `apsp_allEdges_pruned` for the whole saving). -/
theorem apsp_pruned : EndStatement.APSP.SolvedInTime 2.99931 :=
  endStatements_pruned.2.2.2

/-! ## The optimum of the method -/

/-- **The optimum at a ratio `c`.** For the thinness constant `A`, the savings
`ε min(2σ - 1, min(γX(c, θ), σ - q(θ)) - (2σ - 1))` of the admissible parameters `(θ, σ, ε)` have
the least upper bound `R(Γ(c)) Γ(c)/2`, and it is not attained. -/
theorem optimum_at_ratio {A c : ℝ} (hc : 10 < c) (hA : 0 < A) :
    IsLUB {s | ∃ θ σ ε, AdmissibleX A c θ σ ε ∧ s = tupleSaving c θ σ ε} (savingF A (Gam c)) ∧
      savingF A (Gam c) ∉ {s | ∃ θ σ ε, AdmissibleX A c θ σ ε ∧ s = tupleSaving c θ σ ε} :=
  ⟨isLUB_tupleSaving hc hA, savingF_notMem_tupleSaving hA⟩

/-- **The global optimum with pruned encodings.** The supremum over all ratios `c > 10` of the
optimal saving lies in `(0.002095, 0.002096]`, and a ratio whose saving is at least `0.002095` lies
in `(21, 23)`. So the method, with all three ingredients, gives Exact Triangle in `n^{3 - δ}` for
no `δ > 0.002096`, and 3SUM in `n^{2 - δ/2}` for no exponent below `1.998952`. -/
theorem optimum_global :
    (0.002095 : ℝ) < SstarPruned ∧ SstarPruned ≤ 0.002096 ∧
      ∀ c : ℝ, 10 < c → (0.002095 : ℝ) ≤ savingF (basePruned c) (Gam c) →
        c ∈ Set.Ioo (21 : ℝ) 23 :=
  ⟨lt_SstarPruned, SstarPruned_le, mem_Ioo_of_savingF_pruned_ge⟩

/-- **Every saving below the global optimum** of the method with pruned encodings. -/
theorem allSolved_pruned_sup {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < SstarPruned) : AllSolved δ := by
  obtain ⟨c, hc1, -, hs⟩ := exists_savingF_pruned_gt hδ
  exact allSolved_pruned (by linarith) hδ0 hs

/-- **The global optimum with the paper's encodings.** The supremum over all ratios `c > 10` of the
optimal saving lies in `(0.002059, 0.002061]`, and a ratio whose saving is at least `0.002059` lies
in `(20.8, 22)`. This is the optimum of the unconditional theorems: the exact count and the
reduction charged at the true size of the middle part, with the encodings of the paper. -/
theorem optimum_global_full :
    (0.002059 : ℝ) < SstarFull ∧ SstarFull ≤ 0.002061 ∧
      ∀ c : ℝ, 10 < c → (0.002059 : ℝ) ≤ savingF (baseFull c) (Gam c) →
        c ∈ Set.Ioo (20.8 : ℝ) 22 :=
  ⟨lt_SstarFull, SstarFull_le, mem_Ioo_of_savingF_full_ge⟩

/-- **Every saving below the global optimum with the paper's encodings**, with no hypothesis: the
unconditional theorem reaches the optimum of its method. -/
theorem allSolved_full_sup {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < SstarFull) : AllSolved δ := by
  obtain ⟨c, hc1, -, hs⟩ := exists_savingF_full_gt hδ
  exact allSolved_full (by linarith) hδ0 hs

/-! ## APSP through all-edges Exact Triangle

Footnote 10 of the paper: the all-edges version of Exact Triangle is solved by the host of
Theorem 17 within the same bound (`ImprovedExponents.AllEdges.Host`), and the (min,+)-product
reduces to it on the same `n` vertices (`ImprovedExponents.AllEdges.Pairs`, upstream's bit search
and repeated squaring). So the (min,+)-product and APSP keep all of the saving `δ` of Exact
Triangle:
the exponent is `3 - δ` instead of `3 - δ/3`. -/

/-- The two end statements at a rational exponent above `3 - δ`. -/
theorem AllEdges.MinPlusSolved.endStatements {δ : ℝ} (h : AllEdges.MinPlusSolved δ) {rM : ℚ}
    (hM : 3 - δ < (rM : ℝ)) (hM0 : 0 ≤ rM) :
    EndStatement.MinPlusProduct.SolvedInTime rM ∧ EndStatement.APSP.SolvedInTime rM :=
  ⟨SolvedInTime.endStatement (h.minPlus _ hM) rfl hM0,
    SolvedInTime.endStatement (h.apsp _ hM) rfl hM0⟩

/-- **The (min,+)-product and APSP from the saving at a ratio**, with the exact count, the reduction
charged at the true middle size and the all-edges host: every saving below `R_c(Γ(c)) Γ(c)/2`, for
every `c ≥ 20`, with the whole saving. No hypothesis. -/
theorem minPlusSolved_full {c δ : ℝ} (hc : 20 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ < savingF (baseFull c) (Gam c)) : AllEdges.MinPlusSolved δ := by
  have hhalf : savingF (baseFull c) (Gam c) ≤ 1 / 2 :=
    savingF_le_half (baseFull_pos (by linarith)).le (Gam_pos (by linarith)).le
  exact AllEdges.minPlusSolved_of_explicitFrom AllEdges.CA_nonneg AllEdges.pairsFromAllEdges
    (by linarith) (explicitFrom_full hc hδ0 hδ AllEdges.lightModelAE rfl AllEdges.midHostRat_ae)

/-- **Every saving below the global optimum with the paper's encodings**, for the (min,+)-product
and APSP with the whole saving. No hypothesis. -/
theorem minPlusSolved_full_sup {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < SstarFull) :
    AllEdges.MinPlusSolved δ := by
  obtain ⟨c, hc1, -, hs⟩ := exists_savingF_full_gt hδ
  exact minPlusSolved_full (by linarith) hδ0 hs

/-- **The (min,+)-product and APSP with pruned encodings**: every saving below
`R'_c(Γ(c)) Γ(c)/2`, for every `c ≥ 21`, with the whole saving. No hypothesis. -/
theorem minPlusSolved_pruned {c δ : ℝ} (hc : 21 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ < savingF (basePruned c) (Gam c)) : AllEdges.MinPlusSolved δ := by
  have hhalf : savingF (basePruned c) (Gam c) ≤ 1 / 2 :=
    savingF_le_half (basePruned_pos (by linarith)).le (Gam_pos (by linarith)).le
  exact AllEdges.minPlusSolved_of_explicitFrom AllEdges.CA_nonneg AllEdges.pairsFromAllEdges
    (by linarith)
    (explicitFrom_pruned hc hδ0 hδ AllEdges.lightModelAE rfl AllEdges.midHostRat_ae)

/-- **Every saving below the global optimum with pruned encodings**, for the (min,+)-product and
APSP with the whole saving. -/
theorem minPlusSolved_pruned_sup {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < SstarPruned) : AllEdges.MinPlusSolved δ := by
  obtain ⟨c, hc1, -, hs⟩ := exists_savingF_pruned_gt hδ
  exact minPlusSolved_pruned (by linarith) hδ0 hs

/-- The (min,+)-product and APSP in `O(n^2.99795)`: the exact count, the true middle size and the
all-edges host, at `c = 107/5`. -/
theorem endStatements_allEdges :
    EndStatement.MinPlusProduct.SolvedInTime 2.99795 ∧ EndStatement.APSP.SolvedInTime 2.99795 :=
  (minPlusSolved_full (c := 107 / 5) (by norm_num) (by norm_num)
    savingF_full_107_5_gt).endStatements (by norm_num) (by norm_num)

/-- **The (min,+)-product in `O(n^2.99795)` steps on the word RAM.** No hypothesis. -/
theorem minPlus_allEdges : EndStatement.MinPlusProduct.SolvedInTime 2.99795 :=
  endStatements_allEdges.1

/-- **APSP in `O(n^2.99795)` steps on the word RAM.** No hypothesis. -/
theorem apsp_allEdges : EndStatement.APSP.SolvedInTime 2.99795 := endStatements_allEdges.2

/-- The (min,+)-product and APSP in `O(n^2.99791)`, with pruned encodings and the all-edges host,
at `c = 22`. -/
theorem endStatements_allEdges_pruned :
    EndStatement.MinPlusProduct.SolvedInTime 2.99791 ∧ EndStatement.APSP.SolvedInTime 2.99791 :=
  (minPlusSolved_pruned (c := 22) (by norm_num) (by norm_num)
    savingF_pruned_gt).endStatements (by norm_num) (by norm_num)

/-- **The (min,+)-product in `O(n^2.99791)` steps on the word RAM.** No hypothesis. -/
theorem minPlus_allEdges_pruned :
    EndStatement.MinPlusProduct.SolvedInTime 2.99791 :=
  endStatements_allEdges_pruned.1

/-- **APSP in `O(n^2.99791)` steps on the word RAM.** No hypothesis. -/
theorem apsp_allEdges_pruned :
    EndStatement.APSP.SolvedInTime 2.99791 :=
  endStatements_allEdges_pruned.2

end ImprovedExponents
