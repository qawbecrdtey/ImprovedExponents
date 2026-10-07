module

public import ImprovedExponents.Optimum.PerCSupremum

@[expose] public section

/-!
# Rational parameters

Programs can only use rational parameters. This file shows that nothing is lost: the saving
`tupleSaving c θ σ ε` is continuous in all four parameters (`continuous_tupleSaving`), being
admissible is an open condition when the thinness constant `A(c)` depends continuously on `c`, and
the rationals are dense. So near every admissible real tuple there is an admissible rational tuple
with a slightly larger `c`, with `σ > 1/2`, and with almost the same saving (`exists_rat_tuple_gt`).
With `exists_tupleSaving_gt`, every `s < savingF (A c) (Gam c)` is exceeded by the saving of an
admissible rational tuple whose `c′` is as close to `c` as we wish
(`exists_rat_tuple_of_lt_savingF`).
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set Filter Topology

/-- The saving `tupleSaving c θ σ ε` is continuous in `(c, θ, σ, ε)`. -/
theorem continuous_tupleSaving :
    Continuous fun p : ℝ × ℝ × ℝ × ℝ => tupleSaving p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hX : Continuous fun p : ℝ × ℝ × ℝ × ℝ => gammaX p.1 p.2.1 :=
    continuous_gammaX.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hq : Continuous fun p : ℝ × ℝ × ℝ × ℝ => qOf p.2.1 :=
    continuous_qOf.comp (continuous_fst.comp continuous_snd)
  have hσ : Continuous fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1 := by fun_prop
  have hε : Continuous fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2 := by fun_prop
  have hu : Continuous fun p : ℝ × ℝ × ℝ × ℝ => 2 * p.2.2.1 - 1 := by fun_prop
  unfold tupleSaving effGamma
  exact hε.mul (hu.min ((hX.min (hσ.sub hq)).sub hu))

/-- An admissible tuple has a positive denominator `A + γX(c, θ) ln 4` in its thinness bound,
whatever the sign of `A`. -/
theorem AdmissibleX.den_pos {A c θ σ ε : ℝ} (h : AdmissibleX A c θ σ ε) :
    0 < A + gammaX c θ * log 4 := by
  have hpos : 0 < thinR A (gammaX c θ) := h.ε_pos.trans h.thin
  unfold thinR at hpos
  exact (div_pos_iff_of_pos_left log_four_pos).1 hpos

/-- **Rational parameters are as good as real ones**: let the thinness constant `A` be continuous
at `c`. Near every admissible real tuple `(c, θ, σ, ε)` whose saving exceeds `s`, there is an
admissible rational tuple `(c′, θ′, σ′, ε′)` with `c < c′ < c₁`, `σ′ > 1/2`, and saving larger
than `s`. -/
theorem exists_rat_tuple_gt {A : ℝ → ℝ} {c θ σ ε s : ℝ} (hA : ContinuousAt A c)
    (h : AdmissibleX (A c) c θ σ ε) (hs : s < tupleSaving c θ σ ε) (c₁ : ℝ) (hc₁ : c < c₁) :
    ∃ c' θ' σ' ε' : ℚ, c < (c' : ℝ) ∧ (c' : ℝ) < c₁ ∧ (1 / 2 : ℝ) < (σ' : ℝ) ∧
      AdmissibleX (A (c' : ℝ)) (c' : ℝ) (θ' : ℝ) (σ' : ℝ) (ε' : ℝ) ∧
      s < tupleSaving (c' : ℝ) (θ' : ℝ) (σ' : ℝ) (ε' : ℝ) := by
  have hX : Continuous fun p : ℝ × ℝ × ℝ × ℝ => gammaX p.1 p.2.1 :=
    continuous_gammaX.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hθc : Continuous fun p : ℝ × ℝ × ℝ × ℝ => p.2.1 := by fun_prop
  have hσc : Continuous fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1 := by fun_prop
  have hεc : Continuous fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2 := by fun_prop
  -- the thinness bound is continuous at the given tuple
  have hAc : ContinuousAt (fun p : ℝ × ℝ × ℝ × ℝ => A p.1) (c, θ, σ, ε) :=
    ContinuousAt.comp (f := Prod.fst) (x := (c, θ, σ, ε)) hA continuousAt_fst
  have hR : ContinuousAt (fun p : ℝ × ℝ × ℝ × ℝ => thinR (A p.1) (gammaX p.1 p.2.1))
      (c, θ, σ, ε) := by
    unfold thinR
    exact continuousAt_const.div (hAc.add (hX.continuousAt.mul continuousAt_const))
      h.den_pos.ne'
  -- the open conditions hold near the given tuple
  have e1 : ∀ᶠ p : ℝ × ℝ × ℝ × ℝ in 𝓝 (c, θ, σ, ε),
      p.2.2.2 < thinR (A p.1) (gammaX p.1 p.2.1) :=
    hεc.continuousAt.eventually_lt hR h.thin
  have e2 : ∀ᶠ p : ℝ × ℝ × ℝ × ℝ in 𝓝 (c, θ, σ, ε),
      s < tupleSaving p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    continuousAt_const.eventually_lt continuous_tupleSaving.continuousAt hs
  have e3 : ∀ᶠ p : ℝ × ℝ × ℝ × ℝ in 𝓝 (c, θ, σ, ε), p.2.1 < 9 / 10 :=
    hθc.continuousAt.eventually_lt continuousAt_const h.θ_lt
  have e4 : ∀ᶠ p : ℝ × ℝ × ℝ × ℝ in 𝓝 (c, θ, σ, ε), p.2.2.1 < 1 :=
    hσc.continuousAt.eventually_lt continuousAt_const h.σ_lt
  obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 (e1.and (e2.and (e3.and e4)))
  -- rational points slightly above the given ones
  obtain ⟨c', hc'1, hc'2⟩ := exists_rat_btwn (lt_min hc₁ (lt_add_of_pos_right c hδ))
  obtain ⟨θ', hθ'1, hθ'2⟩ := exists_rat_btwn (lt_add_of_pos_right θ hδ)
  obtain ⟨σ', hσ'1, hσ'2⟩ := exists_rat_btwn (lt_add_of_pos_right σ hδ)
  obtain ⟨ε', hε'1, hε'2⟩ := exists_rat_btwn (lt_add_of_pos_right ε hδ)
  have hc'3 : (c' : ℝ) < c₁ := hc'2.trans_le (min_le_left _ _)
  have hc'4 : (c' : ℝ) < c + δ := hc'2.trans_le (min_le_right _ _)
  have hdist : dist ((c' : ℝ), (θ' : ℝ), (σ' : ℝ), (ε' : ℝ)) (c, θ, σ, ε) < δ := by
    simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  obtain ⟨h1, h2, h3, h4⟩ := H hdist
  have hc := h.c_gt
  have hθ := h.θ_pos
  have hσ := h.σ_ge
  have hε := h.ε_pos
  exact ⟨c', θ', σ', ε', hc'1, hc'3, by linarith,
    ⟨by linarith, by linarith, h3, by linarith, h4, by linarith, h1⟩, h2⟩

/-- **Rational tuples approach the supremum**: let `A` be continuous and positive on `(10, ∞)`
and `c > 10`. Every `s < savingF (A c) (Gam c)` is exceeded by the saving of an admissible
rational tuple `(c′, θ′, σ′, ε′)` with `c < c′ < c₁` and `σ′ > 1/2`. -/
theorem exists_rat_tuple_of_lt_savingF' {A : ℝ → ℝ} {c : ℝ} (hc : 10 < c)
    (hA : ContinuousOn A (Ioi 10)) (hApos : ∀ x, 10 < x → 0 < A x) {s : ℝ}
    (hs : s < savingF (A c) (Gam c)) (c₁ : ℝ) (hc₁ : c < c₁) :
    ∃ c' θ' σ' ε' : ℚ, c < (c' : ℝ) ∧ (c' : ℝ) < c₁ ∧ (1 / 2 : ℝ) < (σ' : ℝ) ∧
      AdmissibleX (A (c' : ℝ)) (c' : ℝ) (θ' : ℝ) (σ' : ℝ) (ε' : ℝ) ∧
      s < tupleSaving (c' : ℝ) (θ' : ℝ) (σ' : ℝ) (ε' : ℝ) := by
  obtain ⟨θ, σ, ε, h, hgt⟩ := exists_tupleSaving_gt hc (hApos c hc) hs
  exact exists_rat_tuple_gt (hA.continuousAt (Ioi_mem_nhds hc)) h hgt c₁ hc₁

/-- **Rational tuples approach the supremum**: let `A` be continuous and positive on `(10, ∞)`
and `c > 10`. Every `s < savingF (A c) (Gam c)` is exceeded by the saving of an admissible
rational tuple `(c′, θ′, σ′, ε′)` with `c < c′ < c₁`. -/
theorem exists_rat_tuple_of_lt_savingF {A : ℝ → ℝ} {c : ℝ} (hc : 10 < c)
    (hA : ContinuousOn A (Ioi 10)) (hApos : ∀ x, 10 < x → 0 < A x) {s : ℝ}
    (hs : s < savingF (A c) (Gam c)) (c₁ : ℝ) (hc₁ : c < c₁) :
    ∃ c' θ' σ' ε' : ℚ, c < (c' : ℝ) ∧ (c' : ℝ) < c₁ ∧
      AdmissibleX (A (c' : ℝ)) (c' : ℝ) (θ' : ℝ) (σ' : ℝ) (ε' : ℝ) ∧
      s < tupleSaving (c' : ℝ) (θ' : ℝ) (σ' : ℝ) (ε' : ℝ) := by
  obtain ⟨c', θ', σ', ε', h1, h2, -, h3, h4⟩ :=
    exists_rat_tuple_of_lt_savingF' hc hA hApos hs c₁ hc₁
  exact ⟨c', θ', σ', ε', h1, h2, h3, h4⟩

/-- The case `A = baseFull` (the paper's encodings): every `s < savingF (baseFull c) (Gam c)` is
exceeded by the saving of an admissible rational tuple with `c < c′ < c₁` and `σ′ > 1/2`. -/
theorem exists_rat_tuple_baseFull {c : ℝ} (hc : 10 < c) {s : ℝ}
    (hs : s < savingF (baseFull c) (Gam c)) (c₁ : ℝ) (hc₁ : c < c₁) :
    ∃ c' θ' σ' ε' : ℚ, c < (c' : ℝ) ∧ (c' : ℝ) < c₁ ∧ (1 / 2 : ℝ) < (σ' : ℝ) ∧
      AdmissibleX (baseFull (c' : ℝ)) (c' : ℝ) (θ' : ℝ) (σ' : ℝ) (ε' : ℝ) ∧
      s < tupleSaving (c' : ℝ) (θ' : ℝ) (σ' : ℝ) (ε' : ℝ) :=
  exists_rat_tuple_of_lt_savingF' hc baseFull_continuousOn (fun _ hx => baseFull_pos hx.le) hs
    c₁ hc₁

/-- The case `A = basePruned` (pruned encodings): every `s < savingF (basePruned c) (Gam c)` is
exceeded by the saving of an admissible rational tuple with `c < c′ < c₁` and `σ′ > 1/2`. -/
theorem exists_rat_tuple_basePruned {c : ℝ} (hc : 10 < c) {s : ℝ}
    (hs : s < savingF (basePruned c) (Gam c)) (c₁ : ℝ) (hc₁ : c < c₁) :
    ∃ c' θ' σ' ε' : ℚ, c < (c' : ℝ) ∧ (c' : ℝ) < c₁ ∧ (1 / 2 : ℝ) < (σ' : ℝ) ∧
      AdmissibleX (basePruned (c' : ℝ)) (c' : ℝ) (θ' : ℝ) (σ' : ℝ) (ε' : ℝ) ∧
      s < tupleSaving (c' : ℝ) (θ' : ℝ) (σ' : ℝ) (ε' : ℝ) :=
  exists_rat_tuple_of_lt_savingF' hc basePruned_continuousOn
    (fun _ hx => basePruned_pos (by linarith)) hs c₁ hc₁

end ImprovedExponents
