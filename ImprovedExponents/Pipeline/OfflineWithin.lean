module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.RealParameters
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program

@[expose] public section

/-!
# The time of the offline routine of Section 4, as one statement

The offline routine `offline32` of the upstream program `program31 G` preprocesses and then answers
one query for each wanted position. Its parameters `G : RatParams` are in the program text: the
ratios `c = a/b` and `θ = p/q` and the threshold `m₀` below which it computes inner products.

`OfflineWithinT t ε γ q` says that a routine with the running time `t N D w` takes, on every
instance with `1 ≤ D ≤ N^ε`, at most a constant times

  `N² (log D + 1)²/D^γ + w D^q (log D + 1)`

steps, `w` being the number of wanted positions; `OfflineWithin G ε γ q` is this for the time of
`offline32`. This is the only fact about running times that the solver built on a routine needs
(`ImprovedExponents.Pipeline.ThinClaim`).

Upstream proves it with the paper's exponent `γ = θ ln(1/ρ_c)/ln 4` (`offlineWithin_gammaOf`, a
restatement of `Light.Sec4.exists_ratParams` for parameters that are given rather than chosen).
-/

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4

/-- A routine with the running time `t N D w` takes at most a constant times
`N² (log D + 1)²/D^γ + w D^q (log D + 1)` steps (400 further steps included) on every instance with
`1 ≤ D ≤ N^ε`. -/
def OfflineWithinT (t : ℕ → ℕ → ℕ → ℕ) (ε γ q : ℝ) : Prop :=
  ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
    (t N D₀ w : ℝ) + 400 ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀)

/-- The offline routine at the parameters `G` takes at most a constant times
`N² (log D + 1)²/D^γ + w D^q (log D + 1)` steps (400 further steps included) on every instance with
`1 ≤ D ≤ N^ε`: `OfflineWithinT` of its time `tOffline32 cShared30 G`. -/
def OfflineWithin (G : RatParams) (ε γ q : ℝ) : Prop :=
  OfflineWithinT (tOffline32 cShared30 G) ε γ q

/-- If the two bounds dominate the two costs of Theorem 30 on the instances with `D ≤ N^ε`, the
offline routine stays within them. -/
theorem OfflineWithin.of_costsWithin {G : RatParams} {ε γ q C : ℝ} (hC : 0 ≤ C)
    (h : ∀ N D₀ : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      CostsWithin G C N D₀ (preBound31 γ N D₀) (queryBound31 q D₀)) :
    OfflineWithin G ε γ q := by
  obtain ⟨A, hA⟩ := exists_tOffline32_le G hC cShared30 400
  exact ⟨A, fun N D₀ w hN hD hDN => by exact_mod_cast hA w (h N D₀ hN hD hDN)⟩

section bounds

variable {N D₀ : ℕ}

-- The next six lemmas are adapted from upstream
-- `ThreeSumApsp/Programs/Sec4/ChoosingParameters/RealParameters.lean`, where they are private.

/-- `D ≤ N^ε` with `ε ≤ 1` gives `D ≤ N`. -/
theorem le_of_le_rpow {ε : ℝ} (hN : 1 ≤ N) (hε : ε ≤ 1) (h : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) :
    D₀ ≤ N := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : (D₀ : ℝ) ≤ (N : ℝ) :=
    h.trans ((Real.rpow_le_rpow_of_exponent_le hNR hε).trans_eq (Real.rpow_one _))
  exact_mod_cast this

/-- `D ≤ N^ε` with `ε γ ≤ 1` gives `D^γ ≤ N²`. -/
theorem rpow_le_sq {ε γ : ℝ} (hN : 1 ≤ N) (hγ : 0 ≤ γ) (hεγ : ε * γ ≤ 1)
    (h : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : (D₀ : ℝ) ^ γ ≤ (N : ℝ) ^ 2 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc (D₀ : ℝ) ^ γ ≤ ((N : ℝ) ^ ε) ^ γ := Real.rpow_le_rpow (by positivity) h hγ
    _ = (N : ℝ) ^ (ε * γ) := by rw [← Real.rpow_mul (by positivity)]
    _ ≤ (N : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
    _ = (N : ℝ) ^ 2 := by norm_cast

/-- The bound on the preprocessing is at least 1 if `D^γ ≤ N²`. -/
theorem one_le_preBound31 {γ : ℝ} (hD : 1 ≤ D₀) (h : (D₀ : ℝ) ^ γ ≤ (N : ℝ) ^ 2) :
    1 ≤ preBound31 γ N D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  unfold preBound31
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _), one_mul]
  exact h.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith)))

/-- The bound on a query is at least 1. -/
theorem one_le_queryBound31 {q : ℝ} (hD : 1 ≤ D₀) (hq : 0 ≤ q) : 1 ≤ queryBound31 q D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hDR hq) (by linarith)

/-- A larger exponent of `D` in the denominator, and `log D` in place of `log D + 1`, make the
bound on the preprocessing smaller. -/
theorem le_preBound31 {γ γ' : ℝ} (hD : 1 ≤ D₀) (hγ : γ ≤ γ') :
    (N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ γ' ≤ preBound31 γ N D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  have hsq : Real.log (D₀ : ℝ) ^ 2 ≤ (Real.log D₀ + 1) ^ 2 := pow_le_pow_left₀ hlog (by linarith) 2
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsq (by positivity))
    (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow_of_exponent_le hDR hγ)

/-- A smaller exponent of `D`, and `log D` in place of `log D + 1`, make the bound on a query
smaller. -/
theorem le_queryBound31 {q q' : ℝ} (hD : 1 ≤ D₀) (hq : q' ≤ q) :
    (D₀ : ℝ) ^ q' * Real.log (D₀ : ℝ) ≤ queryBound31 q D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hDR hq) (by linarith) hlog (by positivity)

end bounds

/-- **The offline routine with the paper's exponents**, at given ratios `c = a/b` and `θ = p/q`:
for every `ε < R_c(γ)` and every large enough threshold `m₀`, it stays within the bounds with
`γ = θ ln(1/ρ_c)/ln 4` and `q = (H(θ) + θ ln 9)/ln 4`. -/
theorem offlineWithin_gammaOf {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a)
    (hp : 1 ≤ p) (hθ : 10 * p < 9 * q) {ε : ℝ}
    (hε : ε < Rc ((a : ℝ) / b) (gammaOf ((a : ℝ) / b) ((p : ℝ) / q))) :
    ∃ m₁ : ℕ, ∀ (m₀ : ℕ) (hm₀ : 1 ≤ m₀), m₁ ≤ m₀ →
      OfflineWithin ⟨a, b, p, q, m₀, hb, hq, hc, hp, hθ, hm₀⟩ ε
        (gammaOf ((a : ℝ) / b) ((p : ℝ) / q)) (qOf ((p : ℝ) / q)) := by
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
  have hadm : Admissible ((a : ℝ) / b) ((p : ℝ) / q) ε := ⟨hcR, hθ0, hθ1, hε⟩
  obtain ⟨C, m₁, hC, hcost⟩ := Corollary31.costs hadm
  have hγ := corollary_31_gamma_pos _ _ hcR hθ0
  have hε1 : ε ≤ 1 := by
    have := sec4_Rc_lt_epsStar _ (gammaOf ((a : ℝ) / b) ((p : ℝ) / q)) hcR hγ.le
    have := sec4_epsStar_numeric.2
    linarith
  refine ⟨m₁, fun m₀ hm₀ hm₁ => OfflineWithin.of_costsWithin hC fun N D₀ hN hD hDN =>
    ⟨hN, hD, le_of_le_rpow hN hε1 hDN,
      one_le_preBound31 hD (rpow_le_sq hN hγ.le (eps_mul_gamma_le _ _ ε hcR hγ hε) hDN),
      one_le_queryBound31 hD (qOf_nonneg _ hθ0 hθ1), fun hm => ?_⟩⟩
  have hm1 : 1 ≤ logFour D₀ := le_trans hm₀ hm
  obtain ⟨hfit, hpre, hquery⟩ := hcost D₀ N (logFour D₀) (two_le_of_clog hm1) hDN
    (ceil_logb_four D₀).symm (le_trans hm₁ hm)
  rw [levelsOf_div a _ hb] at hfit hpre hquery
  rw [switchOf_div p _ hq] at hpre hquery
  exact ⟨⟨hm1, RatParams.ten_le_L _ _, RatParams.t_le _ _, hfit⟩,
    hpre.trans (mul_le_mul_of_nonneg_left (le_preBound31 hD le_rfl) hC),
    hquery.trans (mul_le_mul_of_nonneg_left (le_queryBound31 hD le_rfl) hC)⟩

end ImprovedExponents
