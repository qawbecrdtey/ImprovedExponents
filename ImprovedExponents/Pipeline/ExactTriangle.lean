module

public import ImprovedExponents.Pipeline.Claims
public import ImprovedExponents.Pipeline.Choose
public import ImprovedExponents.Pipeline.Solved
public import ImprovedExponents.Total.Explicit
public import ImprovedExponents.Total.Uniform
public import ImprovedExponents.Total.Lop

@[expose] public section

/-!
# Exact Triangle from a thin-product claim

The deduction of Section 3 of the paper for programs, with rational exponents in the program text.

* `explicitFrom_of_thinClaim_orig`: the reduction of Theorem 17 as printed, with
  `D(n) = ⌊n^d⌋` and `g = ⌈D^η⌉`. A thin-product claim with exponents `γ`, `q` on the instances with
  `D ≤ N^ε`, `d < ε`, gives Exact Triangle in time `O(κ n^{3-δ} log n)` for every
  `δ < d min(η, min(γ, 1/2 - q) - η)`.
* `explicitFrom_of_thinClaim_mid`: the reduction that passes the true size of the middle part. With
  the prime size `σ ∈ (1/2, 1)` and the inner dimension `≈ n^e` it runs the host at
  `D' = ⌊n^{2σe}⌋`, `g' = ⌈D'^{(2σ-1)/(2σ)}⌉`, and gives every
  `δ < e min(2σ - 1, min(γ, σ - q) - (2σ - 1))`. It holds in every time model `M` that detects
  Lop-AE-SparseTri as `lightModel` does and has the host at the true size of the middle part
  (`MidHostRat M`); `lightModel` is one (`midHostRat_light`).
* `explicitFrom_tuple`: the second statement for an admissible tuple `(c, θ, σ, ε)` and every `δ`
  below its saving `tupleSaving c θ σ ε`, in the same models.
* `allSolved_of_explicitFrom`: from there to the four problems on the word RAM.
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3 Light.Sec4 ParamRoutines

/-- **From Exact Triangle to the four problems**, for the programs. -/
theorem allSolved_of_explicitFrom {δ : ℝ} {e : ℕ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : ExplicitFrom lightModel δ e) : AllSolved δ :=
  allSolved_of_uniform hδ1 h
    (exactTriangleUniform_of_explicitFrom lightModel e hδ0 hδ1 h claim_bruteForce
      closure_chooseBySize fun _ _ hle hT => SolvedIn.mono hT hle)

/-- The Lop claim from a thin-product claim of the program model, with the exponent capped at 1. -/
theorem lopClaim_of_thinClaim_light {ε γ q : ℝ} (hthin : ThinClaim lightModel ε γ q) (hγ : 0 ≤ γ)
    (hq : 0 ≤ q) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) : LopClaim lightModel ε (min γ 1) q :=
  lopClaim_of_thinClaim lightModel (le_min hγ zero_le_one) hq
    (by nlinarith [min_le_right γ 1, le_min hγ zero_le_one])
    (hthin.mono_gamma (min_le_left _ _)) claim_lopCountFromThinProduct claim_lopDetectFromCount

/-- A Lop claim of `lightModel` is one of every model that detects Lop-AE-SparseTri as `lightModel`
does. -/
theorem LopClaim.of_lopDetect_eq {M : DetTimeModel} (hM : M.lopDetect = lightModel.lopDetect)
    {ε γ q : ℝ} (h : LopClaim lightModel ε γ q) : LopClaim M ε γ q := by
  obtain ⟨C, Td, hTd, hb⟩ := h
  exact ⟨C, Td, by rw [hM]; exact hTd, hb⟩

/-- **The reduction of Theorem 17 as printed**, at rational exponents `d` and `η`. -/
theorem explicitFrom_of_thinClaim_orig {ε γ q δ : ℝ} {d η : ℚ}
    (hthin : ThinClaim lightModel ε γ q) (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hε : ε ≤ 1 / 2)
    (hd0 : 0 < d) (hd : (d : ℝ) < ε) (hη0 : 0 < η) (hη1 : (η : ℝ) < 1 / 2)
    (hδ0 : 0 ≤ δ) (hsmall : 3 / 2 * (d : ℝ) + δ ≤ 19 / 100)
    (hδ : δ < (d : ℝ) * min (η : ℝ) (min γ (1 / 2 - q) - η)) :
    ExplicitFrom lightModel δ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hηR : (0 : ℝ) < η := by exact_mod_cast hη0
  have hlop := lopClaim_of_thinClaim_light hthin hγ hq (hdR.le.trans hd.le) hε
  have hd_eq := rat_eq_div hd0.le
  have hη_eq := rat_eq_div hη0.le
  have hab : d.num.toNat ≤ 2 * d.den := by
    have h := mul_num_lt_mul_den hd0.le (k := 1) (l := 2) (by norm_num)
      (by push_cast; linarith)
    omega
  have hcd : η.num.toNat ≤ 3 * η.den := by
    have h := mul_num_lt_mul_den hη0.le (k := 1) (l := 2) (by norm_num)
      (by push_cast; linarith)
    omega
  have h17 := claim_theorem_17_rat d.num.toNat d.den η.num.toNat η.den d.den_pos η.den_pos
    hab hcd
  have hmin : min (min γ 1) (1 / 2 - q) = min γ (1 / 2 - q) := by
    rw [min_assoc, min_eq_right (by linarith : (1 / 2 - q) ≤ 1)]
  refine explicitFrom_original lightModel hdR hηR hη1 (le_min hγ zero_le_one) hq hδ0 hsmall
    (fun n => ?_) (fun n => ?_) h17 hlop hd (by rwa [hmin])
  · rw [hd_eq]
    rfl
  · rw [hη_eq]
    rfl

/-- **The reduction charged at the true size of the middle part**, at a rational prime size `σ`
and a rational exponent `e` of the inner dimension. -/
theorem explicitFrom_of_thinClaim_mid {ε γ q δ : ℝ} {σ e : ℚ}
    (hthin : ThinClaim lightModel ε γ q) (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hε : ε ≤ 1 / 2)
    (hσ1 : (1 / 2 : ℝ) < σ) (hσ2 : (σ : ℝ) < 1) (he0 : (0 : ℝ) < e) (he : (e : ℝ) < ε)
    (hδ0 : 0 ≤ δ) (hsmall : 3 * (σ : ℝ) * e + δ ≤ 19 / 100)
    (hδ : δ < (e : ℝ) * min (2 * (σ : ℝ) - 1) (min γ (σ - q) - (2 * (σ : ℝ) - 1)))
    (M : DetTimeModel) (hM : M.lopDetect = lightModel.lopDetect) (hhost : MidHostRat M) :
    ExplicitFrom M δ 1 := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  -- the exponents of the host
  set d : ℚ := 2 * σ * e with hd
  set η : ℚ := (2 * σ - 1) / (2 * σ) with hη
  have hdR : (d : ℝ) = 2 * σ * e := by rw [hd]; push_cast; ring
  have hηR : (η : ℝ) = (2 * σ - 1) / (2 * σ) := by rw [hη]; push_cast; ring
  have hd0R : (0 : ℝ) < d := by rw [hdR]; positivity
  have hη0R : (0 : ℝ) < η := by rw [hηR]; exact div_pos (by linarith) (by linarith)
  have hη1R : (η : ℝ) < 1 / 2 := by
    rw [hηR, div_lt_iff₀ (by linarith)]
    linarith
  have hd0 : 0 < d := by exact_mod_cast hd0R
  have hη0 : 0 < η := by exact_mod_cast hη0R
  have hone : 1 - (η : ℝ) = 1 / (2 * σ) := by
    rw [hηR]
    field_simp
    ring
  have hlop := (lopClaim_of_thinClaim_light hthin hγ hq (he0.le.trans he.le) hε).of_lopDetect_eq hM
  have hd_eq := rat_eq_div hd0.le
  have hη_eq := rat_eq_div hη0.le
  have hd1 : (d : ℝ) < 1 := by
    rw [hdR]
    nlinarith
  have hab : d.num.toNat ≤ 2 * d.den := by
    have h := mul_num_lt_mul_den hd0.le (k := 1) (l := 1) (by norm_num)
      (by push_cast; linarith)
    omega
  have hcd : η.num.toNat ≤ 3 * η.den := by
    have h := mul_num_lt_mul_den hη0.le (k := 1) (l := 2) (by norm_num)
      (by push_cast; linarith)
    omega
  have hhost := hhost d.num.toNat d.den η.num.toNat η.den d.den_pos η.den_pos hab hcd
  -- the three exponents, in terms of `σ` and `e`
  have h1 : (d : ℝ) * η = e * (2 * σ - 1) := by
    rw [hdR, hηR]
    field_simp
  have h2 : (d : ℝ) * (min γ 1 * (1 - η)) = e * min γ 1 := by
    rw [hone, hdR]
    field_simp
  have h3 : (d : ℝ) * (1 / 2 - q * (1 - η)) = e * (σ - q) := by
    rw [hone, hdR]
    field_simp
  have hmin : min (min γ 1) ((σ : ℝ) - q) = min γ (σ - q) := by
    rw [min_assoc, min_eq_right (by linarith : (σ : ℝ) - q ≤ 1)]
  have hkey : (d : ℝ) * min (η : ℝ) (min (min γ 1 * (1 - η)) (1 / 2 - q * (1 - η)) - η)
      = e * min (2 * (σ : ℝ) - 1) (min γ (σ - q) - (2 * (σ : ℝ) - 1)) :=
    calc (d : ℝ) * min (η : ℝ) (min (min γ 1 * (1 - η)) (1 / 2 - q * (1 - η)) - η)
        = min ((d : ℝ) * η)
            ((d : ℝ) * (min (min γ 1 * (1 - η)) (1 / 2 - q * (1 - η)) - η)) :=
          mul_min_of_nonneg _ _ hd0R.le
      _ = min ((d : ℝ) * η) (min ((d : ℝ) * (min γ 1 * (1 - η)))
            ((d : ℝ) * (1 / 2 - q * (1 - η))) - (d : ℝ) * η) := by
          rw [mul_sub, mul_min_of_nonneg _ _ hd0R.le]
      _ = min ((e : ℝ) * (2 * σ - 1))
            (min ((e : ℝ) * min γ 1) ((e : ℝ) * (σ - q)) - (e : ℝ) * (2 * σ - 1)) := by
          rw [h1, h2, h3]
      _ = min ((e : ℝ) * (2 * σ - 1))
            ((e : ℝ) * (min (min γ 1) (σ - q) - (2 * σ - 1))) := by
          rw [← mul_min_of_nonneg _ _ he0.le, ← mul_sub]
      _ = (e : ℝ) * min (2 * (σ : ℝ) - 1) (min (min γ 1) (σ - q) - (2 * (σ : ℝ) - 1)) :=
          (mul_min_of_nonneg _ _ he0.le).symm
      _ = e * min (2 * (σ : ℝ) - 1) (min γ (σ - q) - (2 * (σ : ℝ) - 1)) := by rw [hmin]
  refine explicitFrom_mid M (D := paramDRat d.num.toNat d.den)
    (g := paramGRatOf d.num.toNat d.den η.num.toNat η.den) hd0R hη0R hη1R
    (le_min hγ zero_le_one) hq hδ0 (by rw [hdR]; linarith) (fun n => ?_) (fun n => ?_) hhost hlop
    ?_ (by rwa [hkey])
  · rw [hd_eq]
    rfl
  · rw [hη_eq]
    rfl
  · rw [hone, hdR]
    have : 2 * (σ : ℝ) * e * (1 / (2 * σ)) = e := by field_simp
    rw [this]
    exact he

/-- **Exact Triangle at an admissible tuple** `(c, θ, σ, ε)` with a rational prime size `σ > 1/2`:
every `δ` below the saving of the tuple, given the thin-product claims below the exact exponent. -/
theorem explicitFrom_tuple {A c θ ε δ : ℝ} {σ : ℚ} (hadm : AdmissibleX A c θ σ ε)
    (hσ : (1 / 2 : ℝ) < σ) (hε : ε ≤ 1 / 16)
    (hthin : ∀ γ : ℝ, 0 < γ → γ < gammaX c θ → ThinClaim lightModel ε γ (qOf θ))
    (hδ0 : 0 ≤ δ) (hδ : δ < tupleSaving c θ σ ε) (M : DetTimeModel)
    (hM : M.lopDetect = lightModel.lopDetect) (hhost : MidHostRat M) : ExplicitFrom M δ 1 := by
  have hq : 0 ≤ qOf θ := qOf_nonneg θ hadm.θ_pos (by have := hadm.θ_lt; norm_num; linarith)
  unfold tupleSaving effGamma at hδ
  obtain ⟨γ, e, hγlt, he0, he, hδ'⟩ := exists_gamma_rat_of_lt hδ0 hadm.ε_pos hδ
  -- the bracket is positive, hence `γ > 0`
  have hm : 0 < min (2 * (σ : ℝ) - 1) (min γ (σ - qOf θ) - (2 * (σ : ℝ) - 1)) := by
    by_contra hneg
    have : (e : ℝ) * min (2 * (σ : ℝ) - 1) (min γ (σ - qOf θ) - (2 * (σ : ℝ) - 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos he0.le (not_lt.1 hneg)
    linarith
  have hγ0 : 0 < γ := by
    have h1 := (lt_min_iff.1 hm).2
    have h2 := min_le_left γ ((σ : ℝ) - qOf θ)
    linarith
  -- the bracket is at most `min(2σ - 1, 1 - σ) ≤ 1/3`
  have hle : min (2 * (σ : ℝ) - 1) (min γ (σ - qOf θ) - (2 * (σ : ℝ) - 1))
      ≤ min (2 * (σ : ℝ) - 1) (1 - σ) :=
    min_le_min le_rfl (by have := min_le_right γ ((σ : ℝ) - qOf θ); linarith)
  have hthird := min_le_third (σ : ℝ)
  have hσ2 := hadm.σ_lt
  have hw : 3 * (σ : ℝ) + min (2 * (σ : ℝ) - 1) (1 - σ) ≤ 3 := by
    rcases le_total (σ : ℝ) (2 / 3) with h | h
    · have := min_le_left (2 * (σ : ℝ) - 1) (1 - σ)
      linarith
    · have := min_le_right (2 * (σ : ℝ) - 1) (1 - σ)
      linarith
  refine explicitFrom_of_thinClaim_mid (hthin γ hγ0 hγlt) hγ0.le hq (by linarith) hσ hσ2 he0 he
    hδ0 ?_ hδ' M hM hhost
  have hprod : (e : ℝ) * min (2 * (σ : ℝ) - 1) (min γ (σ - qOf θ) - (2 * (σ : ℝ) - 1))
      ≤ e * min (2 * (σ : ℝ) - 1) (1 - σ) := mul_le_mul_of_nonneg_left hle he0.le
  have hall : 3 * (σ : ℝ) * e + (e : ℝ) * min (2 * (σ : ℝ) - 1) (1 - σ) ≤ 3 * e := by
    have := mul_le_mul_of_nonneg_left hw he0.le
    linarith
  linarith

end ImprovedExponents
