module

public import ImprovedExponents.Pipeline.HostBound

@[expose] public section

/-!
# The solver of Lop-AE-SparseTri from a thin-product claim

Corollary 16 for arbitrary exponents: "This is Corollary 26 with N = n, applied to the two
biadjacency matrices". The matrices have entries 0 and 1; writing them down and copying the answers
costs `O(nD + w + 1)`, and telling which counts are nonzero `O(w + 1)`. Both are absorbed by the
bound `n² (log D + 1)²/D^γ + w D^q (log D + 1)` when `D ≤ n^ε` with `ε (1 + γ) ≤ 1`, because then
`D^{1+γ} ≤ n`, that is `n D ≤ n²/D^γ`.
-/

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4

/-- For `1 ≤ D ≤ n^ε` with `ε (1 + γ) ≤ 1`, the size `n D` of the two matrices is at most the bound
on the preprocessing. -/
theorem mul_le_preBound31 {ε γ : ℝ} {n D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D) (hγ : 0 ≤ γ)
    (hε : ε * (1 + γ) ≤ 1) (hDn : (D : ℝ) ≤ (n : ℝ) ^ ε) :
    (n : ℝ) * D ≤ preBound31 γ n D := by
  have hNR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hpow : (D : ℝ) ^ (1 + γ) ≤ n := by
    calc (D : ℝ) ^ (1 + γ) ≤ ((n : ℝ) ^ ε) ^ (1 + γ) :=
          Real.rpow_le_rpow hD0.le hDn (by linarith)
      _ = (n : ℝ) ^ (ε * (1 + γ)) := by rw [← Real.rpow_mul (by positivity)]
      _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR hε
      _ = n := Real.rpow_one _
  have hsplit : (D : ℝ) ^ (1 + γ) = D * (D : ℝ) ^ γ := by rw [Real.rpow_add hD0, Real.rpow_one]
  have hlog := Real.log_nonneg hDR
  have hDγ : 0 < (D : ℝ) ^ γ := Real.rpow_pos_of_pos hD0 _
  rw [preBound31, le_div_iff₀ hDγ]
  calc (n : ℝ) * D * (D : ℝ) ^ γ = n * (D * (D : ℝ) ^ γ) := by ring
    _ ≤ n * n := mul_le_mul_of_nonneg_left (hsplit.symm.trans_le hpow) (by positivity)
    _ = (n : ℝ) ^ 2 * 1 := by ring
    _ ≤ (n : ℝ) ^ 2 * (Real.log D + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith)) (by positivity)

/-- **Corollary 16 for arbitrary exponents**: a thin-product claim gives a solver of
Lop-AE-SparseTri with the same bound, by the two transfer claims of the proof of Corollary 15. -/
theorem lopClaim_of_thinClaim (M : DetTimeModel) {ε γ q : ℝ} (hγ : 0 ≤ γ) (hq : 0 ≤ q)
    (hε : ε * (1 + γ) ≤ 1) (h : ThinClaim M ε γ q) (hlop : Claim.LopCountFromThinProduct M)
    (hdet : Claim.LopDetectFromCount M) : LopClaim M ε γ q := by
  obtain ⟨C, T, hT, hb⟩ := h
  obtain ⟨C₁, hlop⟩ := hlop
  obtain ⟨C₃, hdet⟩ := hdet
  refine ⟨|C| + 2 * |C₁| + |C₃|, _, hdet _ (hlop T hT), fun n D w hn hD hDn => ?_⟩
  have hNR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hnD1 : (1 : ℝ) ≤ (n : ℝ) * D := one_le_mul_of_one_le_of_one_le hNR hDR
  have hnD := mul_le_preBound31 hn hD hγ hε hDn
  have hquery1 : 1 ≤ queryBound31 q D := one_le_queryBound31 hD hq
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hwq : (w : ℝ) ≤ w * queryBound31 q D := le_mul_of_one_le_right hw0 hquery1
  have hB0 : 0 ≤ preBound31 γ n D + w * queryBound31 q D := by linarith
  have h1 : T n D w 1 ≤ |C| * (preBound31 γ n D + w * queryBound31 q D) :=
    (hb n D w 1 hn hD hDn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hB0)
  have h2 : C₁ * ((n : ℝ) * D + w + 1)
      ≤ |C₁| * (2 * (preBound31 γ n D + w * queryBound31 q D)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₁) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  have h3 : C₃ * ((w : ℝ) + 1) ≤ |C₃| * (preBound31 γ n D + w * queryBound31 q D) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₃) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  change T n D w 1 + C₁ * ((n : ℝ) * D + w + 1) + C₃ * ((w : ℝ) + 1)
    ≤ (|C| + 2 * |C₁| + |C₃|) * (preBound31 γ n D + w * queryBound31 q D)
  linarith

end ImprovedExponents
