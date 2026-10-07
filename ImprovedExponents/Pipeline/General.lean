module

public import ImprovedExponents.Pipeline.ExactTriangle
public import ImprovedExponents.Optimum.PerCDensity
public import ImprovedExponents.PrunedEncoding.Costs

@[expose] public section

/-!
# The general theorems

Four statements about programs of upstream's word RAM, each for all parameters of its kind and
each concluding `AllSolved δ` (Exact Triangle in `O(n^a)` for `a > 3 - δ`, 3SUM for `a > 2 - δ/2`,
the (min,+)-product and APSP for `a > 3 - δ/3`).

* `allSolved_paper`: the paper's algorithm with the paper's analysis, at any ratios `c = a/b`,
  `θ = p/q` that the program's regime test admits and any rational exponents `d`, `η` of the
  reduction: every `δ < d min(η, min(γ, 1/2 - q) - η)` with the paper's `γ = θ ln(1/ρ_c)/ln 4`.
* `allSolved_exact`: the same with the exact count of the leaves: any `γ < γX(c, θ)`.
* `allSolved_full`: the exact count together with the reduction that passes the true size of the
  middle part: every `δ` below the optimum `S(c) = R_c(Γ(c)) Γ(c)/2` of the method at the ratio
  `c`, for every `c ≥ 20`. The solver tests `D^r ≤ N^s` with `r/s` between `A(c)/ln 4` and `1/ε`
  (`ImprovedExponents.Pipeline.RegimeRS`), so no condition ties `c` to the regime of upstream's
  test `D^18 ≤ N`.
* `allSolved_pruned_of_claim`: the same with the thinness bound of pruned encodings, `R'_c`, for
  every `c ≥ 21`, from the claim `PrunedEncoderClaim`: a thin-product solver that computes the
  encodings of the leaves with at most `m` symbols `P₀` only. Its mathematics is in
  `ImprovedExponents.PrunedEncoding`; the program is `ImprovedExponents.PrunedProgram`, and the
  claim is proved in `ImprovedExponents.Pipeline.PrunedClaim` (`prunedEncoderClaim`), where the
  theorem becomes `allSolved_pruned`, without hypothesis.

The last three come from `explicitFrom_of_rat_tuple`, `explicitFrom_full` and
`explicitFrom_pruned_of_claim`,
which conclude `ExplicitFrom M δ 1` for every time model `M` that detects Lop-AE-SparseTri as
`lightModel` does and has the host of Theorem 17 at the true size of the middle part
(`MidHostRat M`); `lightModel` is one.
-/

namespace ImprovedExponents

open ThreeSumApsp Light Real

/-! ## The reduction as printed -/

section printed

variable {a b p q : ℕ}

/-- **The paper's algorithm and analysis at better parameters.** -/
theorem allSolved_paper (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a) (hp : 1 ≤ p)
    (hθ : 10 * p < 9 * q) (h18 : basePruned ((a : ℝ) / b) < 18 * log 4) {ε : ℝ}
    (hε : ε < Rc ((a : ℝ) / b) (gammaOf ((a : ℝ) / b) ((p : ℝ) / q))) (hε18 : ε ≤ 1 / 18)
    {d η : ℚ} (hd0 : 0 < d) (hd : (d : ℝ) < ε) (hη0 : 0 < η) (hη1 : (η : ℝ) < 1 / 2) {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hδ : δ < (d : ℝ) * min (η : ℝ)
      (min (gammaOf ((a : ℝ) / b) ((p : ℝ) / q)) (1 / 2 - qOf ((p : ℝ) / q)) - η)) :
    AllSolved δ := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcR : (10 : ℝ) < (a : ℝ) / b := by
    rw [lt_div_iff₀ hbR]
    exact_mod_cast hc
  have hθ0 : (0 : ℝ) < (p : ℝ) / q := div_pos (by exact_mod_cast hp) hqR
  have hθ1 : (p : ℝ) / q < 0.9 := by
    rw [div_lt_iff₀ hqR]
    have h : (10 : ℝ) * p < 9 * q := by exact_mod_cast hθ
    linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hηR : (0 : ℝ) < η := by exact_mod_cast hη0
  have hδle : δ ≤ (d : ℝ) * η := hδ.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdR.le)
  have hdη : (d : ℝ) * η ≤ 1 / 18 * (1 / 2) :=
    mul_le_mul (by linarith) hη1.le hηR.le (by norm_num)
  refine allSolved_of_explicitFrom hδ0 (by linarith) (explicitFrom_of_thinClaim_orig
    (thinClaim_gammaOf hb hq hc hp hθ h18 hε hε18) (corollary_31_gamma_pos _ _ hcR hθ0).le
    (qOf_nonneg _ hθ0 hθ1) (by linarith) hd0 hd hη0 hη1 hδ0 (by linarith) hδ)

/-- **The paper's algorithm with the exact count of the leaves.** -/
theorem allSolved_exact (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a) (hp : 1 ≤ p)
    (hθ : 10 * p < 9 * q) (h18 : basePruned ((a : ℝ) / b) < 18 * log 4) {γ ε : ℝ}
    (hγ0 : 0 < γ) (hγ : γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q))
    (hε : ε < Rc ((a : ℝ) / b) γ) (hε18 : ε ≤ 1 / 18)
    {d η : ℚ} (hd0 : 0 < d) (hd : (d : ℝ) < ε) (hη0 : 0 < η) (hη1 : (η : ℝ) < 1 / 2) {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hδ : δ < (d : ℝ) * min (η : ℝ) (min γ (1 / 2 - qOf ((p : ℝ) / q)) - η)) :
    AllSolved δ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hθ0 : (0 : ℝ) < (p : ℝ) / q := div_pos (by exact_mod_cast hp) hqR
  have hθ1 : (p : ℝ) / q < 0.9 := by
    rw [div_lt_iff₀ hqR]
    have h : (10 : ℝ) * p < 9 * q := by exact_mod_cast hθ
    linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hηR : (0 : ℝ) < η := by exact_mod_cast hη0
  have hδle : δ ≤ (d : ℝ) * η := hδ.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdR.le)
  have hdη : (d : ℝ) * η ≤ 1 / 18 * (1 / 2) :=
    mul_le_mul (by linarith) hη1.le hηR.le (by norm_num)
  refine allSolved_of_explicitFrom hδ0 (by linarith) (explicitFrom_of_thinClaim_orig
    (thinClaim_gammaX hb hq hc hp hθ h18 hγ0 hγ hε hε18) hγ0.le
    (qOf_nonneg _ hθ0 hθ1) (by linarith) hd0 hd hη0 hη1 hδ0 (by linarith) hδ)

end printed

/-! ## The reduction charged at the true size of the middle part -/

/-- `R(γ) ≤ 1/k` if `A ≥ k ln 4`. -/
theorem thinR_le_inv {A γ k : ℝ} (hk : 0 < k) (hA : k * log 4 ≤ A) (hγ : 0 ≤ γ) :
    thinR A γ ≤ 1 / k := by
  have h4 := log_four_pos
  unfold thinR
  rw [div_le_div_iff₀ (by nlinarith) hk]
  nlinarith

/-- **From an admissible tuple of rational numbers**, given thin-product claims at the two ratios
for all exponents below the exact one: Exact Triangle in every model with the host at the true size
of the middle part. -/
theorem explicitFrom_of_rat_tuple {A δ : ℝ} {c θ σ ε : ℚ}
    (hadm : AdmissibleX A (c : ℝ) (θ : ℝ) (σ : ℝ) (ε : ℝ)) (hσ : (1 / 2 : ℝ) < σ)
    (hε : (ε : ℝ) ≤ 1 / 16)
    (hthin : ∀ {a b p q : ℕ}, 1 ≤ b → 1 ≤ q → 10 * b < a → 1 ≤ p → 10 * p < 9 * q →
      (c : ℝ) = (a : ℝ) / b → (θ : ℝ) = (p : ℝ) / q →
      ∀ γ : ℝ, 0 < γ → γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q) →
        ThinClaim lightModel ε γ (qOf ((p : ℝ) / q)))
    (hδ0 : 0 ≤ δ) (hδ : δ < tupleSaving (c : ℝ) (θ : ℝ) (σ : ℝ) (ε : ℝ)) (M : DetTimeModel)
    (hM : M.lopDetect = lightModel.lopDetect) (hhost : MidHostRat M) : ExplicitFrom M δ 1 := by
  have hc0 : (0 : ℚ) ≤ c := by
    have h : (0 : ℝ) ≤ c := by linarith [hadm.c_gt]
    exact_mod_cast h
  have hθ0 : (0 : ℚ) < θ := by exact_mod_cast hadm.θ_pos
  have hc_eq := rat_eq_div hc0
  have hθ_eq := rat_eq_div hθ0.le
  have hcab : 10 * c.den < c.num.toNat := mul_den_lt_num hc0 (by exact_mod_cast hadm.c_gt)
  have hθpq : 10 * θ.num.toNat < 9 * θ.den :=
    mul_num_lt_mul_den hθ0.le (by norm_num) (by exact_mod_cast hadm.θ_lt)
  refine explicitFrom_tuple hadm hσ hε (fun γ hγ0 hγ => ?_) hδ0 hδ M hM hhost
  have h := hthin c.den_pos θ.den_pos hcab (one_le_num_toNat hθ0) hθpq hc_eq hθ_eq γ hγ0
    (by rwa [← hc_eq, ← hθ_eq])
  rwa [← hθ_eq] at h

/-- **From an admissible tuple of rational numbers**, given thin-product claims at the two ratios
for all exponents below the exact one. -/
theorem allSolved_of_rat_tuple {A δ : ℝ} {c θ σ ε : ℚ}
    (hadm : AdmissibleX A (c : ℝ) (θ : ℝ) (σ : ℝ) (ε : ℝ)) (hσ : (1 / 2 : ℝ) < σ)
    (hε : (ε : ℝ) ≤ 1 / 16)
    (hthin : ∀ {a b p q : ℕ}, 1 ≤ b → 1 ≤ q → 10 * b < a → 1 ≤ p → 10 * p < 9 * q →
      (c : ℝ) = (a : ℝ) / b → (θ : ℝ) = (p : ℝ) / q →
      ∀ γ : ℝ, 0 < γ → γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q) →
        ThinClaim lightModel ε γ (qOf ((p : ℝ) / q)))
    (hδ0 : 0 ≤ δ) (hδ : δ < tupleSaving (c : ℝ) (θ : ℝ) (σ : ℝ) (ε : ℝ)) : AllSolved δ := by
  -- the saving is at most `ε`
  have hsav : tupleSaving (c : ℝ) (θ : ℝ) (σ : ℝ) (ε : ℝ) ≤ ε := by
    unfold tupleSaving
    calc (ε : ℝ) * min (2 * (σ : ℝ) - 1) (effGamma c θ σ - (2 * (σ : ℝ) - 1))
        ≤ ε * (2 * (σ : ℝ) - 1) := mul_le_mul_of_nonneg_left (min_le_left _ _) hadm.ε_pos.le
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (by linarith [hadm.σ_lt]) hadm.ε_pos.le
      _ = ε := mul_one _
  exact allSolved_of_explicitFrom hδ0 (by linarith)
    (explicitFrom_of_rat_tuple hadm hσ hε hthin hδ0 hδ lightModel rfl midHostRat_light)

/-- The optimum `R(Γ) Γ/2` is at most `1/2`: `γ ln 4 ≤ A + γ ln 4`. -/
theorem savingF_le_half {A γ : ℝ} (hA : 0 ≤ A) (hγ : 0 ≤ γ) : savingF A γ ≤ 1 / 2 := by
  have h4 := log_four_pos
  unfold savingF thinR
  rcases eq_or_lt_of_le (add_nonneg hA (mul_nonneg hγ h4.le)) with h | h
  · rw [← h, div_zero, zero_mul, zero_div]
    norm_num
  · rw [div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- `ln Λ_c(0) ≥ 16 ln 4` for `c ≥ 20`: at `c = 20`, `20 ln 10 - (ln 20 + 1)/2 - 19 ln 3 ≥ 16 ln 4`,
as `cEntropy 20 = 20 ln 20 - 19 ln 19 ≤ ln 20 + 1`. -/
theorem baseFull_ge_16 {c : ℝ} (hc : 20 ≤ c) : 16 * log 4 ≤ baseFull c := by
  refine le_trans ?_ (baseFull_monotoneOn (Set.mem_Ici.2 (by norm_num)) (Set.mem_Ici.2
    (by linarith)) hc)
  rw [baseFull_eq (by norm_num)]
  -- `cEntropy 20 = 20 ln 20 - 19 ln 19 = ln 20 + 19 ln(20/19) ≤ ln 20 + 1`
  have hent : cEntropy 20 ≤ log 20 + 1 := by
    have h := log_le_sub_one_of_pos (show (0 : ℝ) < 20 / 19 by norm_num)
    rw [log_div (by norm_num) (by norm_num)] at h
    unfold cEntropy
    simp only [negMulLog]
    norm_num
    nlinarith
  -- `40 ln 10 ≥ 32 ln 4 + ln 20 + 38 ln 3 + 1`, as `10^40 ≥ 3 · 4^32 · 20 · 3^38` and `ln 3 ≥ 1`
  have h3 : 1 ≤ log 3 :=
    (le_log_iff_exp_le (by norm_num)).2 (exp_one_lt_d9.le.trans (by norm_num))
  have hnum : 32 * log 4 + log 20 + 38 * log 3 + log 3 ≤ 40 * log 10 := by
    have h : (4 : ℝ) ^ 32 * 20 * 3 ^ 38 * 3 ≤ 10 ^ 40 := by norm_num
    have hlog := log_le_log (by positivity) h
    rw [log_mul (by positivity) (by norm_num), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by norm_num), log_pow, log_pow, log_pow] at hlog
    push_cast at hlog
    linarith
  norm_num
  linarith

/-- **The exact count with the reduction charged at the true size of the middle part**: every
saving below the optimum `R_c(Γ(c)) Γ(c)/2` at the ratio `c ≥ 20`, in every model with the host at
the true size of the middle part. The thin-product solver tests `D^r ≤ N^s` with a rational `r/s`
between `A(c')/ln 4` and `1/ε'` at the rational tuple `(c', θ', σ', ε')`. -/
theorem explicitFrom_full {c δ : ℝ} (hc : 20 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ < savingF (baseFull c) (Gam c)) (M : DetTimeModel)
    (hM : M.lopDetect = lightModel.lopDetect) (hhost : MidHostRat M) : ExplicitFrom M δ 1 := by
  have hc10 : (10 : ℝ) < c := by linarith
  have h4 := log_four_pos
  obtain ⟨c', θ', σ', ε', hc1, -, hσ', hadm, hs⟩ :=
    exists_rat_tuple_baseFull hc10 hδ (c + 1) (by linarith)
  have hc'10 : (10 : ℝ) < c' := by linarith
  have hγX0 : 0 ≤ gammaX (c' : ℝ) (θ' : ℝ) :=
    (gammaX_pos hc'10 hadm.θ_pos (by linarith [hadm.θ_lt])).le
  have hε16 : (ε' : ℝ) ≤ 1 / 16 :=
    hadm.thin.le.trans (thinR_le_inv (by norm_num) (baseFull_ge_16 (by linarith)) hγX0)
  have hε0 : (0 : ℝ) < ε' := hadm.ε_pos
  -- the exponent of the test: `A(c')/ln 4 < r/s < 1/ε'`
  have hA0 : 0 < basePruned (c' : ℝ) := basePruned_pos (by linarith)
  have hlt : basePruned (c' : ℝ) / log 4 < 1 / ε' := by
    have hthin := hadm.thin
    unfold thinR at hthin
    have hle := basePruned_le_baseFull (c := (c' : ℝ)) (by linarith)
    have hγ4 := mul_nonneg hγX0 h4.le
    have hden : 0 < baseFull (c' : ℝ) + gammaX (c' : ℝ) (θ' : ℝ) * log 4 := by linarith
    rw [lt_div_iff₀ hden] at hthin
    rw [div_lt_div_iff₀ h4 hε0]
    nlinarith [mul_le_mul_of_nonneg_left hle hε0.le, mul_nonneg hε0.le hγ4]
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn hlt
  have ht0 : (0 : ℚ) < t := by
    have h : (0 : ℝ) < t := lt_trans (by positivity) ht1
    exact_mod_cast h
  have ht_eq := rat_eq_div ht0.le
  have hr : 1 ≤ t.num.toNat := one_le_num_toNat ht0
  have hs1 : 1 ≤ t.den := t.den_pos
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hrs : basePruned (c' : ℝ) < ((t.num.toNat : ℝ) / t.den) * log 4 := by
    rw [← ht_eq, ← div_lt_iff₀ h4]
    exact ht1
  have hεrs : (ε' : ℝ) ≤ (t.den : ℝ) / t.num.toNat := by
    have hinv : (t.den : ℝ) / t.num.toNat = 1 / t := by
      rw [ht_eq, one_div_div]
    rw [hinv, le_div_iff₀ htR]
    rw [lt_div_iff₀ hε0] at ht2
    linarith
  refine explicitFrom_of_rat_tuple hadm hσ' hε16
    (fun {a b p q} hb hq hcab hp hθ hceq hθeq γ hγ0 hγ => ?_) hδ0 hs M hM hhost
  have hthin : (ε' : ℝ) < Rc ((a : ℝ) / b) γ := by
    have h1 : (ε' : ℝ) < Rc (c' : ℝ) (gammaX (c' : ℝ) (θ' : ℝ)) := by
      rw [Rc_eq_thinR]
      exact hadm.thin
    have h2 : Rc (c' : ℝ) (gammaX (c' : ℝ) (θ' : ℝ)) ≤ Rc (c' : ℝ) γ :=
      (Rc_strictAntiOn_right _ hc'10.le).antitoneOn (Set.mem_Ici.2 hγ0.le)
        (Set.mem_Ici.2 hγX0) (by rw [hceq, hθeq]; exact hγ.le)
    rw [← hceq]
    exact h1.trans_le h2
  exact thinClaimRS_gammaX hb hq hcab hp hθ hr hs1 (by rwa [← hceq]) hγ0 hγ hthin hεrs

/-- **The exact count with the reduction charged at the true size of the middle part**, for the
programs as they are: every saving below the optimum `R_c(Γ(c)) Γ(c)/2` at the ratio `c ≥ 20`. -/
theorem allSolved_full {c δ : ℝ} (hc : 20 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ < savingF (baseFull c) (Gam c)) : AllSolved δ := by
  have hδ1 : δ ≤ 1 := by
    have hA : 0 ≤ baseFull c :=
      (basePruned_pos (c := c) (by linarith)).le.trans (basePruned_le_baseFull (by linarith))
    have h := savingF_le_half hA (Gam_pos (c := c) (by linarith)).le
    linarith
  exact allSolved_of_explicitFrom hδ0 hδ1
    (explicitFrom_full hc hδ0 hδ lightModel rfl midHostRat_light)

/-! ## Pruned encodings: the conditional theorem -/

/-- **The claim on the pruned encoder**: a thin-product solver with pruned encodings.
For all ratios `c = a/b > 10` and `θ = p/q ∈ (0, 0.9)`, every exponent `γ` below the exact one and
every `ε < R'_c(γ)`, the thin product is solved within `N² (log D + 1)²/D^γ + w D^q (log D + 1)`
on the instances with `D ≤ N^ε`. It is `thinClaim_gammaX` with the thinness bound `R'_c` of pruned
encodings in place of `R_c`, and without the restriction to the regime of the existing program's
test. `ImprovedExponents.PrunedEncoding.pruned_encoding` has the mathematics of the encoder, and
`ImprovedExponents.Pipeline.PrunedClaim` proves the claim for the program
`ImprovedExponents.PrunedProgram`. -/
def PrunedEncoderClaim : Prop :=
  ∀ {a b p q : ℕ}, 1 ≤ b → 1 ≤ q → 10 * b < a → 1 ≤ p → 10 * p < 9 * q → ∀ γ ε : ℝ, 0 < γ →
    γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q) → ε < RcP ((a : ℝ) / b) γ →
    ThinClaim lightModel ε γ (qOf ((p : ℝ) / q))

/-- `(c/2) H(1/c) + (c - 1) ln 3 ≥ 16 ln 4` for `c ≥ 21`: already `20 ln 3 + (ln 21)/2 ≥ 16 ln 4`.
-/
theorem basePruned_ge_16 {c : ℝ} (hc : 21 ≤ c) : 16 * log 4 ≤ basePruned c := by
  refine le_trans ?_ (basePruned_monotoneOn (Set.mem_Ici.2 (by norm_num)) (Set.mem_Ici.2
    (by linarith)) hc)
  rw [basePruned_eq (by norm_num)]
  -- `cEntropy 21 = 21 ln 21 - 20 ln 20 ≥ ln 21`
  have hent : log 21 ≤ cEntropy 21 := by
    have h20 : log 20 ≤ log 21 := log_le_log (by norm_num) (by norm_num)
    unfold cEntropy
    simp only [negMulLog]
    norm_num
    nlinarith
  -- `ln 21 + 40 ln 3 ≥ 32 ln 4`, as `21 · 3^40 ≥ 4^32`
  have hnum : 32 * log 4 ≤ log 21 + 40 * log 3 := by
    have h : (4 : ℝ) ^ 32 ≤ 21 * 3 ^ 40 := by norm_num
    have hlog := log_le_log (by positivity) h
    rwa [log_pow, log_mul (by norm_num) (by positivity), log_pow] at hlog
  norm_num
  linarith

/-- **The method with pruned encodings**, from the claim `PrunedEncoderClaim`: every saving
below the optimum `R'_c(Γ(c)) Γ(c)/2` at the ratio `c ≥ 21`, in every model with the host at the
true size of the middle part. -/
theorem explicitFrom_pruned_of_claim (hEnc : PrunedEncoderClaim) {c δ : ℝ} (hc : 21 ≤ c)
    (hδ0 : 0 ≤ δ) (hδ : δ < savingF (basePruned c) (Gam c)) (M : DetTimeModel)
    (hM : M.lopDetect = lightModel.lopDetect) (hhost : MidHostRat M) : ExplicitFrom M δ 1 := by
  have hc10 : (10 : ℝ) < c := by linarith
  obtain ⟨c', θ', σ', ε', hc1, -, hσ', hadm, hs⟩ :=
    exists_rat_tuple_basePruned hc10 hδ (c + 1) (by linarith)
  have hc'10 : (10 : ℝ) < c' := by linarith
  have hγX0 : 0 ≤ gammaX (c' : ℝ) (θ' : ℝ) :=
    (gammaX_pos hc'10 hadm.θ_pos (by linarith [hadm.θ_lt])).le
  have hε16 : (ε' : ℝ) ≤ 1 / 16 :=
    hadm.thin.le.trans (thinR_le_inv (by norm_num) (basePruned_ge_16 (by linarith)) hγX0)
  refine explicitFrom_of_rat_tuple hadm hσ' hε16
    (fun {a b p q} hb hq hcab hp hθ hceq hθeq γ hγ0 hγ => ?_) hδ0 hs M hM hhost
  refine hEnc hb hq hcab hp hθ γ ε' hγ0 hγ ?_
  have h2 : thinR (basePruned (c' : ℝ)) (gammaX (c' : ℝ) (θ' : ℝ))
      ≤ thinR (basePruned (c' : ℝ)) γ :=
    (thinR_strictAntiOn (basePruned_pos (by linarith))).antitoneOn (Set.mem_Ici.2 hγ0.le)
      (Set.mem_Ici.2 hγX0) (by rw [hceq, hθeq]; exact hγ.le)
  rw [RcP, ← hceq]
  exact hadm.thin.trans_le h2

/-- **The method with pruned encodings**, from the claim `PrunedEncoderClaim`: every saving
below the optimum `R'_c(Γ(c)) Γ(c)/2` at the ratio `c`, for `c ≥ 21`. -/
theorem allSolved_pruned_of_claim (hEnc : PrunedEncoderClaim) {c δ : ℝ} (hc : 21 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ < savingF (basePruned c) (Gam c)) : AllSolved δ := by
  have hδ1 : δ ≤ 1 := by
    have h := savingF_le_half (basePruned_pos (c := c) (by linarith)).le
      (Gam_pos (c := c) (by linarith)).le
    linarith
  exact allSolved_of_explicitFrom hδ0 hδ1
    (explicitFrom_pruned_of_claim hEnc hc hδ0 hδ lightModel rfl midHostRat_light)

end ImprovedExponents
