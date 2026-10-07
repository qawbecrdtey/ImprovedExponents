module

public import ImprovedExponents.Optimum.PerCSupremum

@[expose] public section

/-!
# The remark of §6: the supremum of the paper's own accounting

The paper charges every call of the recursion at the inner dimension `D′` of the host, and the
reduction from Exact Triangle then solves it in time `n^{3 - δ}` for every
`δ < d min(η, min(γ, 1/2 - q(θ)) - η)` with `d < ε < R(γ)`, `0 < γ < γX(c, θ)` and `0 < η < 1/2`
(these are the hypotheses of `allSolved_exact` in `Pipeline/General.lean`; the factor `d` may be
taken as close to `ε` as one likes, so it is absorbed into `ε` here). The remark of §6 of the
paper is that, at a ratio `c`, these savings have the least upper bound

  `savingF A (GamHalf c) = R(Γ_H) Γ_H/2`,   `Γ_H(c) = sup_θ min(γX(c, θ), 1/2 - q(θ))`,

the common value of `γX(c, ·)` and `1/2 - q` at their crossing point, and that
`Γ_H(c) < Γ(c)`: the accounting at the true size of the middle part (`Optimum/PerCSupremum.lean`,
with the curve `γ_Q(θ) = (2 - 4 q(θ))/3 > 1/2 - q(θ)` wherever `q(θ) < 1/2`) does strictly better,
`savingF A (GamHalf c) < savingF A (Gam c)`.

The crossing theory is that of `Optimum/PerCCrossing.lean` with the second curve `1/2 - q`, which
is continuous and strictly decreasing on `[0, 9/10]`, from `1/2 > 0 = γX(c, 0)` to
`1/2 - q(9/10) < 0` (`exists_crossing_half`, `crossing_half_unique`, `GamHalf_eq_of_crossing`,
`exists_crossing_eq_GamHalf`, `GamHalf_pos`, `GamHalf_lt_half`, `GamHalf_monotoneOn`). The
supremum is `isLUB_paperSaving`, from the strict bound `paperSaving_lt` and the approximation
`exists_paperSaving_gt`; the comparison is `GamHalf_lt_Gam` and `savingF_GamHalf_lt`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

variable {A c θ θ₀ γ ε η : ℝ}

/-! ### The crossing point of `γX(c, ·)` and `1/2 - q` -/

/-- `Γ_H(c) := sup_{0 < θ < 0.9} min(γX(c, θ), 1/2 - q(θ))`, the best exponent that the paper's
accounting allows. -/
noncomputable def GamHalf (c : ℝ) : ℝ :=
  sSup ((fun θ => min (gammaX c θ) (1 / 2 - qOf θ)) '' Ioo 0 (9 / 10))

/-- `1/2 - q(9/10) < 0`, because `q(9/10) = log_4 10 > 1`. -/
theorem half_sub_qOf_nine_tenths_neg : 1 / 2 - qOf (9 / 10) < 0 := by
  linarith [one_lt_qOf_nine_tenths]

/-- For `c > 10` the functions `γX(c, ·)` and `1/2 - q` cross in `(0, 9/10)`. -/
theorem exists_crossing_half (hc : 10 < c) :
    ∃ θ ∈ Ioo (0 : ℝ) (9 / 10), gammaX c θ = 1 / 2 - qOf θ := by
  have hcont : ContinuousOn (fun θ => gammaX c θ - (1 / 2 - qOf θ)) (Icc 0 (9 / 10)) :=
    ((continuous_gammaX_right c).sub (continuous_const.sub continuous_qOf)).continuousOn
  have h0 : gammaX c 0 - (1 / 2 - qOf 0) < 0 := by
    rw [gammaX_zero, qOf_zero]
    norm_num
  have h1 : 0 < gammaX c (9 / 10) - (1 / 2 - qOf (9 / 10)) := by
    have h := gammaX_pos hc (by norm_num : (0 : ℝ) < 9 / 10) (by norm_num)
    linarith [half_sub_qOf_nine_tenths_neg]
  obtain ⟨θ, hθ, h⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 9 / 10) hcont ⟨h0, h1⟩
  exact ⟨θ, hθ, sub_eq_zero.1 h⟩

/-- The crossing point of `γX(c, ·)` and `1/2 - q` is unique. -/
theorem crossing_half_unique {θ₁ θ₂ : ℝ} (hc : 10 < c) (hθ₁ : θ₁ ∈ Ioo (0 : ℝ) (9 / 10))
    (h₁ : gammaX c θ₁ = 1 / 2 - qOf θ₁) (hθ₂ : θ₂ ∈ Ioo (0 : ℝ) (9 / 10))
    (h₂ : gammaX c θ₂ = 1 / 2 - qOf θ₂) : θ₁ = θ₂ := by
  have hθ₁' := Ioo_subset_Icc_self hθ₁
  have hθ₂' := Ioo_subset_Icc_self hθ₂
  rcases lt_trichotomy θ₁ θ₂ with h | h | h
  · have hX := gammaX_strictMonoOn' hc hθ₁' hθ₂' h
    have hq := qOf_strictMonoOn' hθ₁' hθ₂' h
    linarith
  · exact h
  · have hX := gammaX_strictMonoOn' hc hθ₂' hθ₁' h
    have hq := qOf_strictMonoOn' hθ₂' hθ₁' h
    linarith

/-- At every `θ₀ ∈ [0, 9/10]`, the smaller of `γX(c, θ₀)` and `1/2 - q(θ₀)` is at most the common
value at the crossing point. -/
theorem min_le_of_crossing_half (hc : 10 < c) (hθ : θ ∈ Ioo (0 : ℝ) (9 / 10))
    (h : gammaX c θ = 1 / 2 - qOf θ) (hθ₀ : θ₀ ∈ Icc (0 : ℝ) (9 / 10)) :
    min (gammaX c θ₀) (1 / 2 - qOf θ₀) ≤ gammaX c θ := by
  have hθ' := Ioo_subset_Icc_self hθ
  rcases le_total θ₀ θ with h' | h'
  · exact (min_le_left _ _).trans ((gammaX_strictMonoOn' hc).monotoneOn hθ₀ hθ' h')
  · rw [h]
    have hq := qOf_strictMonoOn'.monotoneOn hθ' hθ₀ h'
    linarith [min_le_right (gammaX c θ₀) (1 / 2 - qOf θ₀)]

/-- `Γ_H(c)` is the common value of `γX(c, ·)` and `1/2 - q` at their crossing point. -/
theorem GamHalf_eq_of_crossing (hc : 10 < c) (hθ : θ ∈ Ioo (0 : ℝ) (9 / 10))
    (h : gammaX c θ = 1 / 2 - qOf θ) : GamHalf c = gammaX c θ := by
  unfold GamHalf
  refine IsGreatest.csSup_eq ⟨⟨θ, hθ, by simp [h]⟩, ?_⟩
  rintro _ ⟨θ₀, hθ₀, rfl⟩
  exact min_le_of_crossing_half hc hθ h (Ioo_subset_Icc_self hθ₀)

/-- For `c > 10` there is `θ₁ ∈ (0, 9/10)` with `γX(c, θ₁) = Γ_H(c) = 1/2 - q(θ₁)`. -/
theorem exists_crossing_eq_GamHalf (hc : 10 < c) :
    ∃ θ ∈ Ioo (0 : ℝ) (9 / 10), gammaX c θ = GamHalf c ∧ 1 / 2 - qOf θ = GamHalf c := by
  obtain ⟨θ, hθ, h⟩ := exists_crossing_half hc
  have hG := GamHalf_eq_of_crossing hc hθ h
  exact ⟨θ, hθ, hG.symm, by rw [← h, hG]⟩

/-- `Γ_H(c) > 0` for `c > 10`. -/
theorem GamHalf_pos (hc : 10 < c) : 0 < GamHalf c := by
  obtain ⟨θ, hθ, hX, -⟩ := exists_crossing_eq_GamHalf hc
  rw [← hX]
  exact gammaX_pos hc hθ.1 (by linarith [hθ.2])

/-- `Γ_H(c) < 1/2` for `c > 10`. -/
theorem GamHalf_lt_half (hc : 10 < c) : GamHalf c < 1 / 2 := by
  obtain ⟨θ, hθ, -, hQ⟩ := exists_crossing_eq_GamHalf hc
  have h := qOf_strictMonoOn' (left_mem_Icc.2 (by norm_num)) (Ioo_subset_Icc_self hθ) hθ.1
  rw [qOf_zero] at h
  linarith

/-- **Lower bound for `Γ_H`**: `min(γX(c, θ₀), 1/2 - q(θ₀)) ≤ Γ_H(c)` for every
`θ₀ ∈ (0, 9/10)`. -/
theorem GamHalf_ge_min (hc : 10 < c) (hθ₀ : θ₀ ∈ Ioo (0 : ℝ) (9 / 10)) :
    min (gammaX c θ₀) (1 / 2 - qOf θ₀) ≤ GamHalf c := by
  obtain ⟨θ, hθ, h⟩ := exists_crossing_half hc
  rw [GamHalf_eq_of_crossing hc hθ h]
  exact min_le_of_crossing_half hc hθ h (Ioo_subset_Icc_self hθ₀)

/-- `Γ_H` is nondecreasing on `(10, ∞)`, because `γX` is nondecreasing in `c`. -/
theorem GamHalf_monotoneOn : MonotoneOn GamHalf (Ioi 10) := by
  intro c₁ hc₁ c₂ hc₂ h
  have hc₁' : (10 : ℝ) < c₁ := hc₁
  have hc₂' : (10 : ℝ) < c₂ := hc₂
  obtain ⟨θ, hθ, hX, hQ⟩ := exists_crossing_eq_GamHalf hc₁'
  have hmono : gammaX c₁ θ ≤ gammaX c₂ θ :=
    gammaX_monotoneOn hθ.1.le (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) h
  calc GamHalf c₁ = min (gammaX c₁ θ) (1 / 2 - qOf θ) := by rw [hX, hQ, min_self]
    _ ≤ min (gammaX c₂ θ) (1 / 2 - qOf θ) := min_le_min_right _ hmono
    _ ≤ GamHalf c₂ := GamHalf_ge_min hc₂' hθ

/-! ### `Γ_H(c) < Γ(c)` -/

/-- **The paper's accounting loses**: `Γ_H(c) < Γ(c)` for `c > 10`. At the crossing point `θ₁` of
`γX(c, ·)` and `1/2 - q` one has `q(θ₁) < 1/2`, so `1/2 - q(θ₁) < (2 - 4 q(θ₁))/3 = γ_Q(θ₁)`: the
curve `γX(c, ·)` is still below `γ_Q` at `θ₁`, so the crossing point `θ*` of `γX(c, ·)` and `γ_Q`
lies to the right of `θ₁`, and `Γ_H(c) = γX(c, θ₁) < γX(c, θ*) = Γ(c)`. -/
theorem GamHalf_lt_Gam (hc : 10 < c) : GamHalf c < Gam c := by
  obtain ⟨θ₁, hθ₁, hX₁, hQ₁⟩ := exists_crossing_eq_GamHalf hc
  obtain ⟨θ₂, hθ₂, hX₂, hQ₂⟩ := exists_crossing_eq_Gam hc
  have hpos := GamHalf_pos hc
  have hlt : gammaX c θ₁ < gammaQ θ₁ := by
    rw [hX₁, gammaQ]
    linarith
  have hθ : θ₁ < θ₂ := by
    refine lt_of_not_ge fun hle => ?_
    have h1 := (gammaX_strictMonoOn' hc).monotoneOn (Ioo_subset_Icc_self hθ₂)
      (Ioo_subset_Icc_self hθ₁) hle
    have h2 := gammaQ_strictAntiOn.antitoneOn (Ioo_subset_Icc_self hθ₂)
      (Ioo_subset_Icc_self hθ₁) hle
    linarith
  rw [← hX₁, ← hX₂]
  exact gammaX_strictMonoOn' hc (Ioo_subset_Icc_self hθ₁) (Ioo_subset_Icc_self hθ₂) hθ

/-! ### The savings of the paper's accounting and their supremum -/

/-- The saving of Exact Triangle at the parameters `(θ, γ, ε, η)` with the paper's accounting:
`ε min(η, min(γ, 1/2 - q(θ)) - η)` (the hypothesis on `δ` of `allSolved_exact`, with the factor
`d < ε` absorbed into `ε`). The ratio `c` enters only through the admissibility of `γ`
(`AdmissibleHalf`). -/
noncomputable def paperSaving (θ γ ε η : ℝ) : ℝ :=
  ε * min η (min γ (1 / 2 - qOf θ) - η)

/-- The parameters that the paper's accounting allows, for the thinness constant `A`. -/
structure AdmissibleHalf (A c θ γ ε η : ℝ) : Prop where
  c_gt : 10 < c
  θ_pos : 0 < θ
  θ_lt : θ < 9 / 10
  γ_pos : 0 < γ
  γ_lt : γ < gammaX c θ
  ε_pos : 0 < ε
  thin : ε < thinR A γ
  η_pos : 0 < η
  η_lt : η < 1 / 2

/-- **The saving of the paper's accounting is below `R(Γ_H) Γ_H/2`**. With
`μ = min(γ, 1/2 - q(θ))` and `v = min(η, μ - η)` one has `2v ≤ μ ≤ Γ_H`, and
`ε v < R(γ) v ≤ R(μ) μ/2 = F(μ) ≤ F(Γ_H)`. -/
theorem paperSaving_lt (hA : 0 < A) (h : AdmissibleHalf A c θ γ ε η) :
    paperSaving θ γ ε η < savingF A (GamHalf c) := by
  have hc := h.c_gt
  have hθ : θ ∈ Ioo (0 : ℝ) (9 / 10) := ⟨h.θ_pos, h.θ_lt⟩
  have hΓ := GamHalf_pos hc
  have hF : 0 < savingF A (GamHalf c) := savingF_pos hA hΓ
  unfold paperSaving
  set μ := min γ (1 / 2 - qOf θ) with hμ
  set v := min η (μ - η) with hv
  rcases le_or_gt v 0 with hv0 | hv0
  · exact (mul_nonpos_of_nonneg_of_nonpos h.ε_pos.le hv0).trans_lt hF
  · have h1 : v ≤ η := min_le_left _ _
    have h2 : v ≤ μ - η := min_le_right _ _
    have hμγ : μ ≤ γ := min_le_left _ _
    have hμq : μ ≤ 1 / 2 - qOf θ := min_le_right _ _
    have hμ0 : 0 < μ := by linarith
    have hμΓ : μ ≤ GamHalf c :=
      (le_min (hμγ.trans h.γ_lt.le) hμq).trans (GamHalf_ge_min hc hθ)
    have hR : thinR A γ ≤ thinR A μ :=
      (thinR_strictAntiOn hA).antitoneOn (mem_Ici.2 hμ0.le) (mem_Ici.2 h.γ_pos.le) hμγ
    calc ε * v < thinR A γ * v := mul_lt_mul_of_pos_right h.thin hv0
      _ ≤ thinR A μ * (μ / 2) :=
          mul_le_mul hR (by linarith) hv0.le (thinR_pos hA hμ0.le).le
      _ = savingF A μ := by
          unfold savingF
          ring
      _ ≤ savingF A (GamHalf c) :=
          (savingF_strictMonoOn hA).monotoneOn (mem_Ici.2 hμ0.le) (mem_Ici.2 hΓ.le) hμΓ

/-- **The bound `R(Γ_H) Γ_H/2` is approached**: every smaller number is exceeded by a saving of
the paper's accounting. At the crossing point `θ₁`, with `η = γ/2`, the saving is `ε γ/2`, where
`γ` may be any number below `Γ_H` and `ε` any number below `R(Γ_H) < R(γ)`. -/
theorem exists_paperSaving_gt (hc : 10 < c) (hA : 0 < A) {s : ℝ}
    (hs : s < savingF A (GamHalf c)) :
    ∃ θ γ ε η, AdmissibleHalf A c θ γ ε η ∧ s < paperSaving θ γ ε η := by
  obtain ⟨θ, hθ, hX, hQ⟩ := exists_crossing_eq_GamHalf hc
  have hΓ := GamHalf_pos hc
  have hΓ' := GamHalf_lt_half hc
  have hR : 0 < thinR A (GamHalf c) := thinR_pos hA hΓ.le
  -- a `γ` below `Γ_H` with `2s < R(Γ_H) γ`
  have hs' : 2 * s / thinR A (GamHalf c) < GamHalf c := by
    rw [div_lt_iff₀ hR]
    unfold savingF at hs
    linarith
  obtain ⟨γ, hγ1, hγ2⟩ := exists_between (max_lt hs' hΓ)
  have hγ0 : 0 < γ := (le_max_right _ _).trans_lt hγ1
  have hγs : 2 * s / thinR A (GamHalf c) < γ := (le_max_left _ _).trans_lt hγ1
  rw [div_lt_iff₀ hR] at hγs
  -- an `ε` below `R(Γ_H)` with `2s < ε γ`
  have hε' : 2 * s / γ < thinR A (GamHalf c) := by
    rw [div_lt_iff₀ hγ0]
    linarith
  obtain ⟨ε, hε1, hε2⟩ := exists_between (max_lt hε' hR)
  have hε0 : 0 < ε := (le_max_right _ _).trans_lt hε1
  have hεs : 2 * s / γ < ε := (le_max_left _ _).trans_lt hε1
  rw [div_lt_iff₀ hγ0] at hεs
  have hthin : ε < thinR A γ :=
    hε2.trans ((thinR_strictAntiOn hA) (mem_Ici.2 hγ0.le) (mem_Ici.2 hΓ.le) hγ2)
  refine ⟨θ, γ, ε, γ / 2,
    ⟨hc, hθ.1, hθ.2, hγ0, by rwa [hX], hε0, hthin, by linarith, by linarith⟩, ?_⟩
  have hmin : min γ (1 / 2 - qOf θ) = γ := min_eq_left (by rw [hQ]; exact hγ2.le)
  rw [paperSaving, hmin, show γ - γ / 2 = γ / 2 by ring, min_self]
  linarith

/-- **The supremum of the savings of the paper's accounting for a fixed `c`**: over the admissible
`(θ, γ, ε, η)`, the least upper bound of `paperSaving θ γ ε η` is
`savingF A (GamHalf c) = R(Γ_H(c)) Γ_H(c)/2`. -/
theorem isLUB_paperSaving (hc : 10 < c) (hA : 0 < A) :
    IsLUB {s | ∃ θ γ ε η, AdmissibleHalf A c θ γ ε η ∧ s = paperSaving θ γ ε η}
      (savingF A (GamHalf c)) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨θ, γ, ε, η, h, rfl⟩
    exact (paperSaving_lt hA h).le
  · by_contra hlt
    obtain ⟨θ, γ, ε, η, h, hgt⟩ := exists_paperSaving_gt hc hA (not_le.1 hlt)
    exact (hb ⟨θ, γ, ε, η, h, rfl⟩).not_gt hgt

/-- **The remark of §6**: the supremum of the savings of the paper's accounting is strictly below
that of the accounting at the true size of the middle part, `R(Γ_H) Γ_H/2 < R(Γ) Γ/2`. -/
theorem savingF_GamHalf_lt (hc : 10 < c) (hA : 0 < A) :
    savingF A (GamHalf c) < savingF A (Gam c) :=
  savingF_strictMonoOn hA (mem_Ici.2 (GamHalf_pos hc).le) (mem_Ici.2 (Gam_pos hc).le)
    (GamHalf_lt_Gam hc)

end ImprovedExponents
