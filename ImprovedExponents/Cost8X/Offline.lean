module

public import ImprovedExponents.Pipeline.OfflineWithin
public import ImprovedExponents.Cost8X.Costs
public import ImprovedExponents.Cost8X.Dominated

@[expose] public section

/-!
# The offline routine of Section 4 with the exact exponent

Upstream's offline routine `offline32` at the ratios `c = a/b` and `θ = p/q` runs within

  `N² (log D + 1)²/D^γ + w D^q (log D + 1)`

steps for the paper's exponent `γ = θ ln(1/ρ_c)/ln 4` (`offlineWithin_gammaOf`). Here the same
program is shown to run within this bound for every `γ` below the exact exponent
`γX(c, θ) = -g₂(c, θ)/ln 4 ≥ θ ln(1/ρ_c)/ln 4`, on the instances with `D ≤ N^ε`, `ε < R_c(γ)`
(`offlineWithinX`). Only the analysis of the running time changes: the number of boxes is bounded
by the exact tail of the leaf counts (`cost8X`) and not by the geometric estimate of the paper.
-/

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4

/-- If the two bounds dominate `cost8X` and the cost of a query on the instances with `D ≤ N^ε`,
the offline routine stays within them. -/
theorem OfflineWithin.of_costsWithinX {G : RatParams} {ε γ q C : ℝ} (hC : 0 ≤ C)
    (h : ∀ N D₀ : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      CostsWithinX G C N D₀ (preBound31 γ N D₀) (queryBound31 q D₀)) :
    OfflineWithin G ε γ q := by
  obtain ⟨A, hA⟩ := exists_tOffline32_leX G hC cShared30 400
  exact ⟨A, fun N D₀ w hN hD hDN => by exact_mod_cast hA w (h N D₀ hN hD hDN)⟩

/-- **The offline routine with the exact exponent**, at given ratios `c = a/b` and `θ = p/q`: for
every `0 < γ < γX(c, θ)`, every `ε < R_c(γ)` and every large enough threshold `m₀`, it stays
within the bounds with the exponents `γ` and `q = (H(θ) + θ ln 9)/ln 4`. -/
theorem offlineWithinX {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a) (hp : 1 ≤ p)
    (hθ : 10 * p < 9 * q) {γ ε : ℝ} (hγ0 : 0 < γ)
    (hγ : γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q)) (hε : ε < Rc ((a : ℝ) / b) γ) :
    ∃ m₁ : ℕ, ∀ (m₀ : ℕ) (hm₀ : 1 ≤ m₀), m₁ ≤ m₀ →
      OfflineWithin ⟨a, b, p, q, m₀, hb, hq, hc, hp, hθ, hm₀⟩ ε γ (qOf ((p : ℝ) / q)) := by
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
  obtain ⟨C, m₁, hC, hcost⟩ := costsX hcR hθ0 hθ1 hγ0.le hγ hε
  have hε1 : ε ≤ 1 := by
    have := sec4_Rc_lt_epsStar _ γ hcR hγ0.le
    have := sec4_epsStar_numeric.2
    linarith
  refine ⟨m₁, fun m₀ hm₀ hm₁ => OfflineWithin.of_costsWithinX hC fun N D₀ hN hD hDN =>
    ⟨hN, hD, le_of_le_rpow hN hε1 hDN,
      one_le_preBound31 hD (rpow_le_sq hN hγ0.le (eps_mul_gamma_le _ _ ε hcR hγ0 hε) hDN),
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
