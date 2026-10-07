module

public import ImprovedExponents.Optimum.PerCCrossing

@[expose] public section

/-!
# The supremum of the savings for a fixed `c`

Fix `c > 10` and a thinness constant `A > 0`. The savings `tupleSaving c θ σ ε` of the admissible
parameters `(θ, σ, ε)` have the least upper bound `savingF A (Gam c) = R(Γ) Γ/2`
(`isLUB_tupleSaving`), and the bound is not attained:

* every admissible tuple has `tupleSaving c θ σ ε < savingF A (Gam c)` (`tupleSaving_lt_savingF`).
  With `a = γX(c, θ)`, `u = 2σ - 1` and `v = min(u, min(a, σ - q) - u) > 0` one has `2v ≤ a` and
  `3v ≤ u + 2((1 - u)/2 - q) = 1 - 2q`, so `2v ≤ μ := min(a, γ_Q(θ)) ≤ Γ`, and
  `ε v < R(a) v ≤ R(μ) μ/2 = F(μ) ≤ F(Γ)`;
* every `s < savingF A (Gam c)` is exceeded (`exists_tupleSaving_gt`): at the crossing point `θ*`
  and `σ = 1/2 + Γ/4` the saving is `ε Γ/2` (`tupleSaving_crossing`), and `ε` may be any number
  below `R(Γ)`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

variable {A c θ σ ε : ℝ}

/-- **The saving of an admissible tuple is below `R(Γ) Γ/2`**. -/
theorem tupleSaving_lt_savingF (hA : 0 < A) (h : AdmissibleX A c θ σ ε) :
    tupleSaving c θ σ ε < savingF A (Gam c) := by
  have hc := h.c_gt
  have hθ : θ ∈ Ioo (0 : ℝ) (9 / 10) := ⟨h.θ_pos, h.θ_lt⟩
  have hΓ := Gam_pos hc
  have hF : 0 < savingF A (Gam c) := savingF_pos hA hΓ
  have ha : 0 < gammaX c θ := gammaX_pos hc h.θ_pos (by linarith [h.θ_lt])
  unfold tupleSaving effGamma
  set v := min (2 * σ - 1) (min (gammaX c θ) (σ - qOf θ) - (2 * σ - 1)) with hv
  rcases le_or_gt v 0 with hv0 | hv0
  · exact (mul_nonpos_of_nonneg_of_nonpos h.ε_pos.le hv0).trans_lt hF
  · have h1 : v ≤ 2 * σ - 1 := min_le_left _ _
    have h2 : v ≤ min (gammaX c θ) (σ - qOf θ) - (2 * σ - 1) := min_le_right _ _
    have h3 : min (gammaX c θ) (σ - qOf θ) ≤ gammaX c θ := min_le_left _ _
    have h4 : min (gammaX c θ) (σ - qOf θ) ≤ σ - qOf θ := min_le_right _ _
    have hva : 2 * v ≤ gammaX c θ := by linarith
    have hvq : 2 * v ≤ gammaQ θ := by
      unfold gammaQ
      linarith
    set μ := min (gammaX c θ) (gammaQ θ) with hμ
    have hμv : 2 * v ≤ μ := le_min hva hvq
    have hμΓ : μ ≤ Gam c := Gam_ge_min hc hθ
    have hμa : μ ≤ gammaX c θ := min_le_left _ _
    have hμ0 : 0 < μ := by linarith
    have hR : thinR A (gammaX c θ) ≤ thinR A μ :=
      (thinR_strictAntiOn hA).antitoneOn (mem_Ici.2 hμ0.le) (mem_Ici.2 ha.le) hμa
    calc ε * v < thinR A (gammaX c θ) * v := mul_lt_mul_of_pos_right h.thin hv0
      _ ≤ thinR A μ * (μ / 2) :=
          mul_le_mul hR (by linarith) hv0.le (thinR_pos hA hμ0.le).le
      _ = savingF A μ := by
          unfold savingF
          ring
      _ ≤ savingF A (Gam c) :=
          (savingF_strictMonoOn hA).monotoneOn (mem_Ici.2 hμ0.le) (mem_Ici.2 hΓ.le) hμΓ

/-- At the crossing point `θ*` and the balanced prime size `σ = 1/2 + Γ/4`, the saving is
`ε Γ/2`. -/
theorem tupleSaving_crossing (hX : gammaX c θ = Gam c) (hQ : gammaQ θ = Gam c) (ε : ℝ) :
    tupleSaving c θ (1 / 2 + Gam c / 4) ε = ε * (Gam c / 2) := by
  have hq : qOf θ = 1 / 2 - 3 * Gam c / 4 := gammaQ_eq_iff.1 hQ
  have e1 : 1 / 2 + Gam c / 4 - qOf θ = Gam c := by
    rw [hq]
    ring
  have e2 : 2 * (1 / 2 + Gam c / 4) - 1 = Gam c / 2 := by ring
  have e3 : Gam c - Gam c / 2 = Gam c / 2 := by ring
  rw [tupleSaving, effGamma, hX, e1, e2, min_self, e3, min_self]

/-- **The bound `R(Γ) Γ/2` is approached**: every smaller number is exceeded by the saving of an
admissible tuple. -/
theorem exists_tupleSaving_gt (hc : 10 < c) (hA : 0 < A) {s : ℝ}
    (hs : s < savingF A (Gam c)) :
    ∃ θ σ ε, AdmissibleX A c θ σ ε ∧ s < tupleSaving c θ σ ε := by
  obtain ⟨θ, hθ, hX, hQ⟩ := exists_crossing_eq_Gam hc
  have hΓ := Gam_pos hc
  have hΓ' := Gam_lt_two_thirds hc
  have hR : 0 < thinR A (Gam c) := thinR_pos hA hΓ.le
  have hs' : s / (Gam c / 2) < thinR A (Gam c) := by
    rw [div_lt_iff₀ (by linarith)]
    unfold savingF at hs
    linarith
  obtain ⟨ε, hε1, hε2⟩ := exists_between (max_lt hs' hR)
  have hε0 : 0 < ε := (le_max_right _ _).trans_lt hε1
  have hεs : s / (Gam c / 2) < ε := (le_max_left _ _).trans_lt hε1
  refine ⟨θ, 1 / 2 + Gam c / 4, ε, ⟨hc, hθ.1, hθ.2, by linarith, by linarith, hε0, ?_⟩, ?_⟩
  · rwa [hX]
  · rw [tupleSaving_crossing hX hQ]
    rwa [div_lt_iff₀ (by linarith)] at hεs

/-- **The supremum of the savings for a fixed `c`**: over the admissible `(θ, σ, ε)`, the least
upper bound of `tupleSaving c θ σ ε` is `savingF A (Gam c) = R(Γ(c)) Γ(c)/2`. -/
theorem isLUB_tupleSaving (hc : 10 < c) (hA : 0 < A) :
    IsLUB {s | ∃ θ σ ε, AdmissibleX A c θ σ ε ∧ s = tupleSaving c θ σ ε}
      (savingF A (Gam c)) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨θ, σ, ε, h, rfl⟩
    exact (tupleSaving_lt_savingF hA h).le
  · by_contra hlt
    obtain ⟨θ, σ, ε, h, hgt⟩ := exists_tupleSaving_gt hc hA (not_le.1 hlt)
    exact (hb ⟨θ, σ, ε, h, rfl⟩).not_gt hgt

/-- The supremum of the savings for a fixed `c` is not attained. -/
theorem savingF_notMem_tupleSaving (hA : 0 < A) :
    savingF A (Gam c) ∉ {s | ∃ θ σ ε, AdmissibleX A c θ σ ε ∧ s = tupleSaving c θ σ ε} := by
  rintro ⟨θ, σ, ε, h, heq⟩
  exact (tupleSaving_lt_savingF hA h).ne' heq

end ImprovedExponents
