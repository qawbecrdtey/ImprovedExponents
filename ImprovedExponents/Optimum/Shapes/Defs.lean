module

public import ImprovedExponents.Optimum.Defs

@[expose] public section

/-!
# The saving of the method for other shapes of the identity: definitions

The constants of `Optimum/Defs.lean` encode Schönhage's identity of shape `(3, 3)`: `s = 9` outer
outputs (the terms other than `P₀`; the identity has ten terms), inner length `b = 4`
(`D = 4^m`), and `N₀ = 3^{L-m} = √s^{L-m}`. The paper's Table 2 evaluates the same analysis for
the other shapes `(k, n)` of the family, with `s = kn` and `b = (k - 1)(n - 1)`. This file has the
functions of the saving with the two natural numbers `s` and `b` as parameters, and the bridges to
the functions of `Optimum/Defs.lean` at `s = 9`, `b = 4`:

* `g2S s c δ = ψ(c - 1) - ψ(c - 1 + δ) - ψ(1 - δ) + δ ln s` and `gammaXS s b c θ = -g2S/ln b`,
  the exact exponent of the boxes (`g2S_nine`, `gammaXS_nine_four`);
* `qS s b θ = (H(θ) + θ ln s)/ln b` and `gammaQS s b θ = (2 - 4 qS)/3` (`qS_nine_four`,
  `gammaQS_nine_four`);
* `GamS s b c = sup_{0 < θ < s/(s+1)} min(gammaXS, gammaQS)` (`GamS_nine_four`); the window of
  `θ` ends where `q` reaches `log_b(s + 1)`, which is `9/10` for `s = 9`;
* `thinRS b A γ = ln b/(A + γ ln b)` and `savingS b A γ = thinRS γ/2` (`thinRS_four`,
  `savingS_four`);
* `basePrunedS s c = (c/2) H(1/c) + (c - 1) (ln s)/2`, the thinness constant with pruned encodings
  (`basePrunedS_nine`; `ln 9/2 = ln 3`);
* `shapeSaving s b c = savingS b (basePrunedS s c) (GamS s b c)`, the saving at the ratio `c`
  (`shapeSaving_nine_four`).

The analysis needs `c > s + 1` (so that `ρ = s m/(L - m + 1) < 1`) and `b < (s + 1)²` (so that
`gammaQS` becomes negative at the end of the window); every shape of the family satisfies the
latter.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

/-- The exponent `g₂` for an identity with `s` terms other than `P₀`:
`ψ(c - 1) - ψ(c - 1 + δ) - ψ(1 - δ) + δ ln s`, with `ψ(x) = x ln x`. -/
noncomputable def g2S (s : ℕ) (c δ : ℝ) : ℝ :=
  negMulLog (c - 1 + δ) - negMulLog (c - 1) + negMulLog (1 - δ) + δ * log s

/-- The exact exponent of the boxes for the shape `(s, b)`: `γX = -g₂/ln b`, since `D = b^m`. -/
noncomputable def gammaXS (s b : ℕ) (c θ : ℝ) : ℝ := -g2S s c θ / log b

/-- The exponent `q = (H(θ) + θ ln s)/ln b` of the number of leaves of order at most `θm`. -/
noncomputable def qS (s b : ℕ) (θ : ℝ) : ℝ := (entropy θ + θ * log s) / log b

/-- `γ_Q = (2 - 4 q)/3`, the largest `γ` with `γ ≤ σ - q` at the balanced prime size
`σ = 1/2 + γ/4`. -/
noncomputable def gammaQS (s b : ℕ) (θ : ℝ) : ℝ := (2 - 4 * qS s b θ) / 3

/-- `Γ(c) = sup_{0 < θ < s/(s+1)} min(γX(c, θ), γ_Q(θ))`, the best exponent of a thin product. -/
noncomputable def GamS (s b : ℕ) (c : ℝ) : ℝ :=
  sSup ((fun θ => min (gammaXS s b c θ) (gammaQS s b θ)) '' Ioo 0 ((s : ℝ) / (s + 1)))

/-- The thinness bound `R(γ) = ln b/(A + γ ln b)` for an inner length `b`. -/
noncomputable def thinRS (b : ℕ) (A γ : ℝ) : ℝ := log b / (A + γ * log b)

/-- The saving `R(γ) γ/2` at the exponent `γ`, for an inner length `b`. -/
noncomputable def savingS (b : ℕ) (A γ : ℝ) : ℝ := thinRS b A γ * γ / 2

/-- The thinness constant with pruned encodings for `s` outer outputs:
`(c/2) H(1/c) + (c - 1) (ln s)/2`, the exponential rate of `√K N₀` with `N₀ = √s^{L-m}`. -/
noncomputable def basePrunedS (s : ℕ) (c : ℝ) : ℝ :=
  c / 2 * entropy (1 / c) + (c - 1) * log s / 2

/-- The saving of the method with pruned encodings for the shape `(s, b)` at the ratio `c`. -/
noncomputable def shapeSaving (s b : ℕ) (c : ℝ) : ℝ := savingS b (basePrunedS s c) (GamS s b c)

/-! ### The bridges to the shape `(3, 3)` -/

/-- `g2S 9 = g₂`. -/
theorem g2S_nine : g2S 9 = g2 := by
  funext c δ
  simp [g2S, g2]

/-- `gammaXS 9 4 = γX`. -/
theorem gammaXS_nine_four : gammaXS 9 4 = gammaX := by
  funext c θ
  simp [gammaXS, gammaX, g2S_nine]

/-- `qS 9 4 = q`. -/
theorem qS_nine_four : qS 9 4 = qOf := by
  funext θ
  simp [qS, qOf]

/-- `gammaQS 9 4 = γ_Q`. -/
theorem gammaQS_nine_four : gammaQS 9 4 = gammaQ := by
  funext θ
  simp [gammaQS, gammaQ, qS_nine_four]

/-- `GamS 9 4 = Γ`. -/
theorem GamS_nine_four : GamS 9 4 = Gam := by
  funext c
  simp only [GamS, Gam, gammaXS_nine_four, gammaQS_nine_four]
  norm_num

/-- `thinRS 4 = thinR`. -/
theorem thinRS_four : thinRS 4 = thinR := by
  funext A γ
  simp [thinRS, thinR]

/-- `savingS 4 = savingF`. -/
theorem savingS_four : savingS 4 = savingF := by
  funext A γ
  simp [savingS, savingF, thinRS_four]

/-- `basePrunedS 9 = basePruned`, because `ln 9 = 2 ln 3`. -/
theorem basePrunedS_nine : basePrunedS 9 = basePruned := by
  funext c
  have h : log (9 : ℝ) = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]
    push_cast
    ring
  simp only [basePrunedS, basePruned, Nat.cast_ofNat, h]
  ring

/-- `shapeSaving 9 4 c = savingF (basePruned c) (Gam c)`: the saving of `Optimum/Defs.lean`. -/
theorem shapeSaving_nine_four (c : ℝ) : shapeSaving 9 4 c = savingF (basePruned c) (Gam c) := by
  rw [shapeSaving, savingS_four, basePrunedS_nine, GamS_nine_four]

end ImprovedExponents
