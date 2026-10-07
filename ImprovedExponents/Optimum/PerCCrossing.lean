module

public import ImprovedExponents.Optimum.PerCBasic

@[expose] public section

/-!
# The crossing point of `γX(c, ·)` and `γ_Q`

Fix `c > 10`. On `[0, 9/10]` the function `γX(c, ·)` is continuous and strictly increasing from
`γX(c, 0) = 0`, and `γ_Q` is continuous and strictly decreasing from `γ_Q(0) = 2/3` to
`γ_Q(9/10) < 0`. So they cross at exactly one point `θ* ∈ (0, 9/10)` (`existsUnique_crossing`),
and `Γ(c) = sup_θ min(γX(c, θ), γ_Q(θ))` is their common value there (`Gam_eq_of_crossing`,
`exists_crossing_eq_Gam`). Consequences:

* `0 < Γ(c) < 2/3` (`Gam_pos`, `Gam_lt_two_thirds`);
* `min(γX(c, θ₀), γ_Q(θ₀)) ≤ Γ(c) ≤ max(γX(c, θ₀), γ_Q(θ₀))` for every `θ₀ ∈ (0, 9/10)`
  (`Gam_ge_min`, `Gam_le_max`);
* `Γ` is nondecreasing on `(10, ∞)` (`Gam_monotoneOn`).
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

variable {c θ θ₀ : ℝ}

/-- For `c > 10` the functions `γX(c, ·)` and `γ_Q` cross in `(0, 9/10)`. -/
theorem exists_crossing (hc : 10 < c) : ∃ θ ∈ Ioo (0 : ℝ) (9 / 10), gammaX c θ = gammaQ θ := by
  have hcont : ContinuousOn (fun θ => gammaX c θ - gammaQ θ) (Icc 0 (9 / 10)) :=
    ((continuous_gammaX_right c).sub continuous_gammaQ).continuousOn
  have h0 : gammaX c 0 - gammaQ 0 < 0 := by
    rw [gammaX_zero, gammaQ_zero]
    norm_num
  have h1 : 0 < gammaX c (9 / 10) - gammaQ (9 / 10) := by
    have h := gammaX_pos hc (by norm_num : (0 : ℝ) < 9 / 10) (by norm_num)
    linarith [gammaQ_nine_tenths_neg]
  obtain ⟨θ, hθ, h⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 9 / 10) hcont ⟨h0, h1⟩
  exact ⟨θ, hθ, sub_eq_zero.1 h⟩

/-- `γX(c, ·)` increases strictly on `[0, 9/10]`, for `c > 10`. -/
theorem gammaX_strictMonoOn' (hc : 10 < c) : StrictMonoOn (gammaX c) (Icc 0 (9 / 10)) :=
  (gammaX_strictMonoOn hc).mono (Icc_subset_Icc_right (by norm_num))

/-- The crossing point is unique. -/
theorem crossing_unique {θ₁ θ₂ : ℝ} (hc : 10 < c) (hθ₁ : θ₁ ∈ Ioo (0 : ℝ) (9 / 10))
    (h₁ : gammaX c θ₁ = gammaQ θ₁) (hθ₂ : θ₂ ∈ Ioo (0 : ℝ) (9 / 10))
    (h₂ : gammaX c θ₂ = gammaQ θ₂) : θ₁ = θ₂ := by
  have hθ₁' := Ioo_subset_Icc_self hθ₁
  have hθ₂' := Ioo_subset_Icc_self hθ₂
  rcases lt_trichotomy θ₁ θ₂ with h | h | h
  · have hX := gammaX_strictMonoOn' hc hθ₁' hθ₂' h
    have hQ := gammaQ_strictAntiOn hθ₁' hθ₂' h
    linarith
  · exact h
  · have hX := gammaX_strictMonoOn' hc hθ₂' hθ₁' h
    have hQ := gammaQ_strictAntiOn hθ₂' hθ₁' h
    linarith

/-- **The crossing point**: for `c > 10` there is exactly one `θ* ∈ (0, 9/10)` with
`γX(c, θ*) = γ_Q(θ*)`. -/
theorem existsUnique_crossing (hc : 10 < c) :
    ∃! θ, θ ∈ Ioo (0 : ℝ) (9 / 10) ∧ gammaX c θ = gammaQ θ := by
  obtain ⟨θ, hθ, h⟩ := exists_crossing hc
  exact ⟨θ, ⟨hθ, h⟩, fun θ' h' => crossing_unique hc h'.1 h'.2 hθ h⟩

/-- At every `θ₀ ∈ [0, 9/10]`, the smaller of `γX(c, θ₀)` and `γ_Q(θ₀)` is at most the common
value at the crossing point. -/
theorem min_le_of_crossing (hc : 10 < c) (hθ : θ ∈ Ioo (0 : ℝ) (9 / 10))
    (h : gammaX c θ = gammaQ θ) (hθ₀ : θ₀ ∈ Icc (0 : ℝ) (9 / 10)) :
    min (gammaX c θ₀) (gammaQ θ₀) ≤ gammaX c θ := by
  have hθ' := Ioo_subset_Icc_self hθ
  rcases le_total θ₀ θ with h' | h'
  · exact (min_le_left _ _).trans ((gammaX_strictMonoOn' hc).monotoneOn hθ₀ hθ' h')
  · rw [h]
    exact (min_le_right _ _).trans (gammaQ_strictAntiOn.antitoneOn hθ' hθ₀ h')

/-- At every `θ₀ ∈ [0, 9/10]`, the larger of `γX(c, θ₀)` and `γ_Q(θ₀)` is at least the common
value at the crossing point. -/
theorem le_max_of_crossing (hc : 10 < c) (hθ : θ ∈ Ioo (0 : ℝ) (9 / 10))
    (h : gammaX c θ = gammaQ θ) (hθ₀ : θ₀ ∈ Icc (0 : ℝ) (9 / 10)) :
    gammaX c θ ≤ max (gammaX c θ₀) (gammaQ θ₀) := by
  have hθ' := Ioo_subset_Icc_self hθ
  rcases le_total θ θ₀ with h' | h'
  · exact ((gammaX_strictMonoOn' hc).monotoneOn hθ' hθ₀ h').trans (le_max_left _ _)
  · rw [h]
    exact (gammaQ_strictAntiOn.antitoneOn hθ₀ hθ' h').trans (le_max_right _ _)

/-- `Γ(c)` is the common value of `γX(c, ·)` and `γ_Q` at their crossing point. -/
theorem Gam_eq_of_crossing (hc : 10 < c) (hθ : θ ∈ Ioo (0 : ℝ) (9 / 10))
    (h : gammaX c θ = gammaQ θ) : Gam c = gammaX c θ := by
  unfold Gam
  refine IsGreatest.csSup_eq ⟨⟨θ, hθ, by simp [h]⟩, ?_⟩
  rintro _ ⟨θ₀, hθ₀, rfl⟩
  exact min_le_of_crossing hc hθ h (Ioo_subset_Icc_self hθ₀)

/-- For `c > 10` there is `θ* ∈ (0, 9/10)` with `γX(c, θ*) = Γ(c) = γ_Q(θ*)`. -/
theorem exists_crossing_eq_Gam (hc : 10 < c) :
    ∃ θ ∈ Ioo (0 : ℝ) (9 / 10), gammaX c θ = Gam c ∧ gammaQ θ = Gam c := by
  obtain ⟨θ, hθ, h⟩ := exists_crossing hc
  have hG := Gam_eq_of_crossing hc hθ h
  exact ⟨θ, hθ, hG.symm, by rw [← h, hG]⟩

/-- A point of `(0, 9/10)` at which `γX(c, ·)` and `γ_Q` both equal `Γ(c)` is the crossing
point. -/
theorem eq_of_gammaX_eq_Gam {θ₁ θ₂ : ℝ} (hc : 10 < c) (hθ₁ : θ₁ ∈ Ioo (0 : ℝ) (9 / 10))
    (h₁ : gammaX c θ₁ = Gam c) (hθ₂ : θ₂ ∈ Ioo (0 : ℝ) (9 / 10)) (h₂ : gammaX c θ₂ = Gam c) :
    θ₁ = θ₂ :=
  (gammaX_strictMonoOn' hc).injOn (Ioo_subset_Icc_self hθ₁) (Ioo_subset_Icc_self hθ₂)
    (h₁.trans h₂.symm)

/-- `Γ(c) > 0` for `c > 10`. -/
theorem Gam_pos (hc : 10 < c) : 0 < Gam c := by
  obtain ⟨θ, hθ, hX, -⟩ := exists_crossing_eq_Gam hc
  rw [← hX]
  exact gammaX_pos hc hθ.1 (by linarith [hθ.2])

/-- `Γ(c) < 2/3` for `c > 10`. -/
theorem Gam_lt_two_thirds (hc : 10 < c) : Gam c < 2 / 3 := by
  obtain ⟨θ, hθ, -, hQ⟩ := exists_crossing_eq_Gam hc
  rw [← hQ, ← gammaQ_zero]
  exact gammaQ_strictAntiOn (left_mem_Icc.2 (by norm_num)) (Ioo_subset_Icc_self hθ) hθ.1

/-- **Lower bound for `Γ`**: `min(γX(c, θ₀), γ_Q(θ₀)) ≤ Γ(c)` for every `θ₀ ∈ (0, 9/10)`. -/
theorem Gam_ge_min (hc : 10 < c) (hθ₀ : θ₀ ∈ Ioo (0 : ℝ) (9 / 10)) :
    min (gammaX c θ₀) (gammaQ θ₀) ≤ Gam c := by
  obtain ⟨θ, hθ, h⟩ := exists_crossing hc
  rw [Gam_eq_of_crossing hc hθ h]
  exact min_le_of_crossing hc hθ h (Ioo_subset_Icc_self hθ₀)

/-- **Upper bound for `Γ`**: `Γ(c) ≤ max(γX(c, θ₀), γ_Q(θ₀))` for every `θ₀ ∈ (0, 9/10)`. -/
theorem Gam_le_max (hc : 10 < c) (hθ₀ : θ₀ ∈ Ioo (0 : ℝ) (9 / 10)) :
    Gam c ≤ max (gammaX c θ₀) (gammaQ θ₀) := by
  obtain ⟨θ, hθ, h⟩ := exists_crossing hc
  rw [Gam_eq_of_crossing hc hθ h]
  exact le_max_of_crossing hc hθ h (Ioo_subset_Icc_self hθ₀)

/-- `Γ` is nondecreasing on `(10, ∞)`, because `γX` is nondecreasing in `c`. -/
theorem Gam_monotoneOn : MonotoneOn Gam (Ioi 10) := by
  intro c₁ hc₁ c₂ hc₂ h
  have hc₁' : (10 : ℝ) < c₁ := hc₁
  have hc₂' : (10 : ℝ) < c₂ := hc₂
  obtain ⟨θ, hθ, hX, hQ⟩ := exists_crossing_eq_Gam hc₁'
  have hmono : gammaX c₁ θ ≤ gammaX c₂ θ :=
    gammaX_monotoneOn hθ.1.le (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) h
  calc Gam c₁ = min (gammaX c₁ θ) (gammaQ θ) := by rw [hX, hQ, min_self]
    _ ≤ min (gammaX c₂ θ) (gammaQ θ) := min_le_min_right _ hmono
    _ ≤ Gam c₂ := Gam_ge_min hc₂' hθ

end ImprovedExponents
