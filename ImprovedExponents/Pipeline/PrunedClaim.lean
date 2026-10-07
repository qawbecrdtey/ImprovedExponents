module

public import ImprovedExponents.Pipeline.General
public import ImprovedExponents.Cost8P.Offline
public import ImprovedExponents.PrunedProgram.Wrapper.Program

@[expose] public section

/-!
# The hypothesis on the pruned encoder, proved

`PrunedEncoderClaim` (`ImprovedExponents.Pipeline.General`) says that a thin-product solver with
pruned encodings meets the time bound of the mathematics of
`ImprovedExponents.PrunedEncoding`: for all rational ratios `c = a/b > 10` and `θ = p/q < 0.9`,
every `0 < γ < γX(c, θ)` and every `ε < R'_c(γ)`, the thin product is solved in the sense of
`ThinClaim lightModel ε γ q(θ)`.  The solver is `programP G r s`
(`ImprovedExponents.PrunedProgram.Wrapper.Program`): upstream's program with the regime test
`D^r ≤ N^s` and the pruned encoder.  Its running time is within the bounds by the cost analysis
`ImprovedExponents.Cost8P` (`offlineWithinP`), the tile fits in the regime by `exists_fitsRS`, and
the generic solver of `ImprovedExponents.Pipeline.ThinClaim` puts the two together
(`thinClaimRS_of_offlineWithinT`).  The exponent `r/s` is chosen strictly between
`A'(c)/ln 4` and `1/ε`, which is possible because `ε < R'_c(γ) < ln 4/A'(c)`; for `ε ≤ 0` the
claim follows from the one at a positive `ε` (`ThinClaim.mono`).

So `prunedEncoderClaim` discharges the one hypothesis of the paper, and the theorems of
`ImprovedExponents.Pipeline.General` that assumed it hold outright: `explicitFrom_pruned` and
`allSolved_pruned`, every saving below the optimum `R'_c(Γ(c)) Γ(c)/2` of the method with pruned
encodings at every ratio `c ≥ 21`.
-/

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4 Real

/-- **The thin product with pruned encodings and the regime test `D^r ≤ N^s`**, at the ratios
`c = a/b` and `θ = p/q` with `A'(c) < (r/s) ln 4`: every exponent `γ < γX(c, θ)`, for
`ε < R'_c(γ)` and `ε ≤ s/r`. -/
-- adapted from ImprovedExponents/Pipeline/Claims.lean (thinClaimRS_gammaX)
theorem thinClaimP_gammaX {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a) (hp : 1 ≤ p)
    (hθ : 10 * p < 9 * q) {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hrs : basePruned ((a : ℝ) / b) < ((r : ℝ) / s) * log 4) {γ ε : ℝ}
    (hγ0 : 0 < γ) (hγ : γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q))
    (hε : ε < RcP ((a : ℝ) / b) γ) (hεrs : ε ≤ (s : ℝ) / r) :
    ThinClaim lightModel ε γ (qOf ((p : ℝ) / q)) := by
  obtain ⟨m₁, h₁⟩ := offlineWithinP cShared30 hb hq hc hp hθ hγ0 hγ hε
  obtain ⟨m₂, h₂⟩ := exists_fitsRS hb hq hc hp hθ hr hs hrs
  have hm₀ : 1 ≤ max (max m₁ m₂) 1 := le_max_right _ _
  obtain ⟨hoff, hauxO, hall⟩ :=
    offline32PRoutine_programP ⟨a, b, p, q, max (max m₁ m₂) 1, hb, hq, hc, hp, hθ, hm₀⟩ r s
  exact thinClaimRS_of_offlineWithinT (O := offline32PRoutine _ r s) hr
    (h₂ _ hm₀ ((le_max_right _ _).trans (le_max_left _ _))) ⟨_, rfl⟩ hall hoff hauxO hεrs
    (h₁ _ hm₀ ((le_max_left _ _).trans (le_max_left _ _)))

/-- **The hypothesis on the pruned encoder holds**: the solver `programP G r s` meets it. -/
theorem prunedEncoderClaim : PrunedEncoderClaim := by
  intro a b p q hb hq hc hp hθ γ ε hγ0 hγ hε
  have h4 := log_four_pos
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hc10 : (10 : ℝ) < (a : ℝ) / b := by
    rw [lt_div_iff₀ hbR]; exact_mod_cast hc
  have hA0 : 0 < basePruned ((a : ℝ) / b) := basePruned_pos (by linarith)
  have hR0 : 0 < RcP ((a : ℝ) / b) γ := thinR_pos hA0 hγ0.le
  -- a positive thinness below `R'_c(γ)`; for `ε ≤ 0` the claim follows from the one at `ε₀`
  set ε₀ := max ε (RcP ((a : ℝ) / b) γ / 2) with hε₀def
  have hε0 : 0 < ε₀ := lt_of_lt_of_le (half_pos hR0) (le_max_right _ _)
  have hε₀ : ε₀ < RcP ((a : ℝ) / b) γ := max_lt hε (by linarith)
  refine ThinClaim.mono (ε₀ := ε₀) (le_max_left _ _) ?_
  -- the exponent of the test: `A'(c)/ln 4 < r/s < 1/ε₀`
  have hlt : basePruned ((a : ℝ) / b) / log 4 < 1 / ε₀ := by
    have hthin := hε₀
    unfold RcP thinR at hthin
    have hγ4 := mul_nonneg hγ0.le h4.le
    have hden : 0 < basePruned ((a : ℝ) / b) + γ * log 4 := by linarith
    rw [lt_div_iff₀ hden] at hthin
    rw [div_lt_div_iff₀ h4 hε0]
    nlinarith [mul_nonneg hε0.le hγ4]
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn hlt
  have ht0 : (0 : ℚ) < t := by
    have h : (0 : ℝ) < t := lt_trans (by positivity) ht1
    exact_mod_cast h
  have ht_eq := rat_eq_div ht0.le
  have hr : 1 ≤ t.num.toNat := one_le_num_toNat ht0
  have hs1 : 1 ≤ t.den := t.den_pos
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hrs : basePruned ((a : ℝ) / b) < ((t.num.toNat : ℝ) / t.den) * log 4 := by
    rw [← ht_eq, ← div_lt_iff₀ h4]
    exact ht1
  have hεrs : ε₀ ≤ (t.den : ℝ) / t.num.toNat := by
    have hinv : (t.den : ℝ) / t.num.toNat = 1 / t := by
      rw [ht_eq, one_div_div]
    rw [hinv, le_div_iff₀ htR]
    rw [lt_div_iff₀ hε0] at ht2
    linarith
  exact thinClaimP_gammaX hb hq hc hp hθ hr hs1 hrs hγ0 hγ hε₀ hεrs

/-- **The method with pruned encodings**: every saving below the optimum `R'_c(Γ(c)) Γ(c)/2` at
the ratio `c ≥ 21`, in every model with the host at the true size of the middle part. No
hypothesis. -/
theorem explicitFrom_pruned {c δ : ℝ} (hc : 21 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ < savingF (basePruned c) (Gam c)) (M : DetTimeModel)
    (hM : M.lopDetect = lightModel.lopDetect) (hhost : MidHostRat M) : ExplicitFrom M δ 1 :=
  explicitFrom_pruned_of_claim prunedEncoderClaim hc hδ0 hδ M hM hhost

/-- **The method with pruned encodings**: every saving below the optimum `R'_c(Γ(c)) Γ(c)/2` at
the ratio `c`, for `c ≥ 21`. No hypothesis. -/
theorem allSolved_pruned {c δ : ℝ} (hc : 21 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ < savingF (basePruned c) (Gam c)) : AllSolved δ :=
  allSolved_pruned_of_claim prunedEncoderClaim hc hδ0 hδ

end ImprovedExponents
