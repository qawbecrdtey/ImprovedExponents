module

public import ImprovedExponents.Pipeline.ThinClaim
public import ImprovedExponents.Optimum.PerCBasic

@[expose] public section

/-!
# Choosing parameters below a saving

Small facts used when the parameters of the programs are fitted to a target saving `δ`.

* A thin-product claim stays true for a smaller exponent `γ` (`ThinClaim.mono_gamma`).
* A nonnegative rational is the quotient of two natural numbers (`rat_eq_div`), which is how
  rational exponents enter the program text.
* If `δ` is below the saving `ε min(u, min(γ, s) - u)`, it is still below it after `γ` is lowered a
  little and `ε` is replaced by a suitable smaller rational (`exists_gamma_rat_of_lt`).
* `min(2σ - 1, 1 - σ) ≤ 1/3`, which bounds every saving by `ε/3` (`min_le_third`).
-/

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4

/-- A thin-product claim with the exponent `γ` gives the claim with every smaller exponent. -/
theorem ThinClaim.mono_gamma {M : DetTimeModel} {ε γ γ' q : ℝ} (h : ThinClaim M ε γ q)
    (hγ : γ' ≤ γ) : ThinClaim M ε γ' q := by
  obtain ⟨C, T, hT, hb⟩ := h
  refine ⟨max C 0, T, hT, fun N D w u hN hD hDN => ?_⟩
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  have hpre : preBound31 γ N D ≤ preBound31 γ' N D := by
    unfold preBound31
    exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hDR hγ)
  have hpre0 : 0 ≤ preBound31 γ N D := by unfold preBound31; positivity
  have hq0 : 0 ≤ (w : ℝ) * queryBound31 q D := by unfold queryBound31; positivity
  calc T N D w u ≤ C * (preBound31 γ N D + (w : ℝ) * queryBound31 q D) := hb N D w u hN hD hDN
    _ ≤ max C 0 * (preBound31 γ N D + (w : ℝ) * queryBound31 q D) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hpre0 hq0)
    _ ≤ max C 0 * (preBound31 γ' N D + (w : ℝ) * queryBound31 q D) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)

/-- A nonnegative rational number is the quotient of two natural numbers. -/
theorem rat_eq_div {r : ℚ} (hr : 0 ≤ r) : (r : ℝ) = (r.num.toNat : ℝ) / (r.den : ℝ) := by
  have hnum : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg (Rat.num_nonneg.2 hr))
  rw [hnum, Rat.cast_def]

/-- The numerator of a positive rational number, as a natural number, is positive. -/
theorem one_le_num_toNat {r : ℚ} (hr : 0 < r) : 1 ≤ r.num.toNat := by
  have h : 0 < r.num := Rat.num_pos.2 hr
  omega

/-- The numerator and the denominator of a rational number between two bounds given by natural
numbers: `k < r` gives `k · den < num`. -/
theorem mul_den_lt_num {r : ℚ} (hr : 0 ≤ r) {k : ℕ} (h : (k : ℝ) < (r : ℝ)) :
    k * r.den < r.num.toNat := by
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  rw [rat_eq_div hr, lt_div_iff₀ hden] at h
  exact_mod_cast h

/-- `r < k/l` for natural `k`, `l` gives `l · num < k · den`. -/
theorem mul_num_lt_mul_den {r : ℚ} (hr : 0 ≤ r) {k l : ℕ} (hl : 0 < l)
    (h : (r : ℝ) < (k : ℝ) / l) : l * r.num.toNat < k * r.den := by
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  rw [rat_eq_div hr, div_lt_div_iff₀ hden hlR] at h
  have h' : (l : ℝ) * (r.num.toNat : ℝ) < (k : ℝ) * (r.den : ℝ) := by linarith
  exact_mod_cast h'

/-- `min(2σ - 1, 1 - σ) ≤ 1/3`. -/
theorem min_le_third (σ : ℝ) : min (2 * σ - 1) (1 - σ) ≤ 1 / 3 := by
  rcases le_total σ (2 / 3) with h | h
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

/-- The function `γ ↦ min(u, min(γ, s) - u)` does not drop by more than `γ` does. -/
theorem min_sub_le (u s γ τ : ℝ) (hτ : 0 ≤ τ) :
    min u (min γ s - u) - τ ≤ min u (min (γ - τ) s - u) := by
  rcases le_total γ s with h | h
  · rw [min_eq_left h, min_eq_left (by linarith : γ - τ ≤ s)]
    rcases le_total u (γ - u) with h1 | h1
    · rw [min_eq_left h1]
      exact le_min (by linarith) (by linarith)
    · rw [min_eq_right h1]
      exact le_min (by linarith) (by linarith)
  · rw [min_eq_right h]
    rcases le_total (γ - τ) s with h2 | h2
    · rw [min_eq_left h2]
      exact le_min (by have := min_le_left u (s - u); linarith)
        (by have := min_le_right u (s - u); linarith)
    · rw [min_eq_right h2]
      linarith

/-- **Lowering the parameters a little.** If `0 ≤ δ < ε min(u, min(γ₀, s) - u)`, there are a
smaller exponent `γ < γ₀` and a positive rational `e < ε` with `δ < e min(u, min(γ, s) - u)`. -/
theorem exists_gamma_rat_of_lt {δ ε u s γ₀ : ℝ} (hδ0 : 0 ≤ δ) (hε : 0 < ε)
    (hδ : δ < ε * min u (min γ₀ s - u)) :
    ∃ (γ : ℝ) (e : ℚ), γ < γ₀ ∧ 0 < (e : ℝ) ∧ (e : ℝ) < ε ∧
      δ < (e : ℝ) * min u (min γ s - u) := by
  set m₀ := min u (min γ₀ s - u) with hm₀
  have hm₀pos : 0 < m₀ := by
    by_contra hneg
    have : ε * m₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le (not_lt.1 hneg)
    linarith
  set τ := (ε * m₀ - δ) / (2 * ε) with hτ
  have hτpos : 0 < τ := div_pos (by linarith) (by positivity)
  set m := min u (min (γ₀ - τ) s - u) with hm
  have hmge : m₀ - τ ≤ m := min_sub_le u s γ₀ τ hτpos.le
  have hετ : ε * τ = (ε * m₀ - δ) / 2 := by
    rw [hτ]
    field_simp
  have hεm : δ < ε * m := by
    have : ε * (m₀ - τ) ≤ ε * m := mul_le_mul_of_nonneg_left hmge hε.le
    nlinarith
  have hmpos : 0 < m := by
    by_contra hneg
    have : ε * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le (not_lt.1 hneg)
    linarith
  have hlt : δ / m < ε := by rwa [div_lt_iff₀ hmpos]
  obtain ⟨e, he1, he2⟩ := exists_rat_btwn hlt
  have he0 : 0 < (e : ℝ) := lt_of_le_of_lt (div_nonneg hδ0 hmpos.le) he1
  refine ⟨γ₀ - τ, e, by linarith, he0, he2, ?_⟩
  rwa [div_lt_iff₀ hmpos] at he1

end ImprovedExponents
