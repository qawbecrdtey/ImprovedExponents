module

public import ImprovedExponents.Optimum.NumLog

@[expose] public section

/-!
# Rational witnesses at `c = 108/5` and density `κ = 1/2`

Two tuples of rational parameters at `c = 108/5` (for which `18 ln 4 ≤ baseFull c`) and `κ = 1/2`,
with the paper's encodings (the thinness bound is `R_c` of equation (11)).

* `t2_witness`: with the paper's exponent `γ = θ ln(1/ρ_c)/ln 4`, the tuple `θ = 0.1127`,
  `γ = 0.0673`, `γ' = 0.0674`, `ε = 0.055` gives `ε γ/2 = 0.00185075 > 0.00184`.
* `t3_witness`: with the exact exponent `γX`, the tuple `θ = 0.11138`, `γ = 0.07139`,
  `ε = 0.05505` gives `ε γ/2 = 0.0019650… > 0.00196`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

/-- `ε < R_c(γ)` at `c = 108/5`, from `baseFull (108/5) ≤ 25.08`. -/
theorem lt_Rc_108_5 {ε γ : ℝ} (hγ : 0 ≤ γ := by numlog) (hε : 0 ≤ ε := by numlog)
    (h : ε * (25.08 + γ * (2 * logTwoHi)) < 2 * logTwoLo := by numlog) : ε < Rc (108 / 5) γ := by
  rw [Rc_eq_thinR]
  exact lt_thinR (baseFull_pos (by norm_num)) (baseFull_le 4 : baseFull (108 / 5) ≤ 25.08) hγ
    le_rfl hε h

/-- **The paper's exponents at `c = 108/5` and `κ = 1/2`**: rational `θ`, `γ ≤ γ(c, θ) ≤ γ'` and
`ε < R_c(γ')` with `q(θ) ≤ 1/2 - γ` and `ε γ/2 > 0.00184`. -/
theorem t2_witness : ∃ θ γ γ' ε : ℚ, (0 : ℝ) < θ ∧ (θ : ℝ) < 9 / 10 ∧ (0 : ℝ) < γ ∧
    (γ : ℝ) ≤ gammaOf (108 / 5) θ ∧ gammaOf (108 / 5) θ ≤ γ' ∧ qOf θ ≤ 1 / 2 - γ ∧ (0 : ℝ) < ε ∧
    (ε : ℝ) < Rc (108 / 5) γ' ∧ (0.00184 : ℝ) < ε * (γ / 2) := by
  have hg : gammaOf (108 / 5) 1 ∈ Icc (0.59732 : ℝ) 0.59733 := gammaOf_one_mem (log_mem 1 4)
  have hm := gammaOf_mem (θ := 1127 / 10000) hg (by norm_num) (by norm_num) ⟨le_rfl, le_rfl⟩
  have hq : qOf (1127 / 10000) ≤ 1 / 2 - 673 / 10000 := qOf_le (-3)
  have hR : (11 / 200 : ℝ) < Rc (108 / 5) (674 / 10000) := lt_Rc_108_5
  refine ⟨1127 / 10000, 673 / 10000, 674 / 10000, 11 / 200, ?_⟩
  push_cast
  exact ⟨by norm_num, by norm_num, by norm_num, le_trans (by norm_num) hm.1,
    hm.2.trans (by norm_num), hq, by norm_num, hR, by norm_num⟩

/-- **The exact count at `c = 108/5` and `κ = 1/2`**: rational `θ`, `γ < γX(c, θ)` and
`ε < R_c(γ)` with `q(θ) ≤ 1/2 - γ` and `ε γ/2 > 0.00196`. -/
theorem t3_witness : ∃ θ γ ε : ℚ, (0 : ℝ) < θ ∧ (θ : ℝ) < 9 / 10 ∧ (0 : ℝ) < γ ∧
    (γ : ℝ) < gammaX (108 / 5) θ ∧ qOf θ ≤ 1 / 2 - γ ∧ (0 : ℝ) < ε ∧
    (ε : ℝ) < Rc (108 / 5) γ ∧ (0.00196 : ℝ) < ε * (γ / 2) := by
  have hX : (0.071395 : ℝ) ≤ gammaX (108 / 5) (11138 / 100000) := le_gammaX 4
  have hq : qOf (11138 / 100000) ≤ 1 / 2 - 7139 / 100000 := qOf_le (-3)
  have hR : (5505 / 100000 : ℝ) < Rc (108 / 5) (7139 / 100000) := lt_Rc_108_5
  refine ⟨11138 / 100000, 7139 / 100000, 5505 / 100000, ?_⟩
  push_cast
  exact ⟨by norm_num, by norm_num, by norm_num, lt_of_lt_of_le (by norm_num) hX, hq,
    by norm_num, hR, by norm_num⟩

end ImprovedExponents
