module

public import ThreeSumApsp.Sec3.Parameters

@[expose] public section

/-!
# Products of powers of `n`: the arithmetic of the total time

The total time of the reduction of Theorem 17 is a sum of six products. Each factor of a product is
at most a constant times a power of `n`, so the product is at most a constant times `n^E` as soon as
the exponents add up to at most `E` (`prod5_le`). A factor `(log n + 1)^3` is at most a constant
times `n^τ`, for every `τ > 0` (`log_add_one_pow_three_le`). `total_le` adds up the six bounds.
-/

namespace ImprovedExponents

/-- A product of five nonnegative factors, each at most a constant times a power of `N ≥ 1`, is at
most the product of the constants times `N^E`, if the exponents add up to at most `E`. -/
theorem prod5_le {N x₁ x₂ x₃ x₄ x₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ E : ℝ} (hN : 1 ≤ N)
    (h0₂ : 0 ≤ x₂) (h0₃ : 0 ≤ x₃) (h0₄ : 0 ≤ x₄) (h0₅ : 0 ≤ x₅)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) (hc₅ : 0 ≤ c₅)
    (h₁ : x₁ ≤ c₁ * N ^ e₁) (h₂ : x₂ ≤ c₂ * N ^ e₂) (h₃ : x₃ ≤ c₃ * N ^ e₃)
    (h₄ : x₄ ≤ c₄ * N ^ e₄) (h₅ : x₅ ≤ c₅ * N ^ e₅) (hE : e₁ + e₂ + e₃ + e₄ + e₅ ≤ E) :
    x₁ * x₂ * x₃ * x₄ * x₅ ≤ c₁ * c₂ * c₃ * c₄ * c₅ * N ^ E := by
  have hN0 : 0 < N := by linarith
  calc x₁ * x₂ * x₃ * x₄ * x₅
      ≤ c₁ * N ^ e₁ * (c₂ * N ^ e₂) * (c₃ * N ^ e₃) * (c₄ * N ^ e₄) * (c₅ * N ^ e₅) := by gcongr
    _ = c₁ * c₂ * c₃ * c₄ * c₅ * N ^ (e₁ + e₂ + e₃ + e₄ + e₅) := by
        rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0]
        ring
    _ ≤ c₁ * c₂ * c₃ * c₄ * c₅ * N ^ E :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hE) (by positivity)

/-- `(log N + 1)^3 ≤ (3/τ + 1)^3 N^τ` for `N ≥ 1` and `τ > 0`. -/
theorem log_add_one_pow_three_le {N τ : ℝ} (hN : 1 ≤ N) (hτ : 0 < τ) :
    (Real.log N + 1) ^ 3 ≤ (3 / τ + 1) ^ 3 * N ^ τ := by
  have hN0 : 0 < N := by linarith
  have h3 : 0 < τ / 3 := by positivity
  have hlog : Real.log N ≤ N ^ (τ / 3) / (τ / 3) := Real.log_le_rpow_div hN0.le h3
  have hone : 1 ≤ N ^ (τ / 3) := Real.one_le_rpow hN h3.le
  have hle : Real.log N + 1 ≤ (3 / τ + 1) * N ^ (τ / 3) := by
    have : N ^ (τ / 3) / (τ / 3) = 3 / τ * N ^ (τ / 3) := by field_simp
    linarith
  have hcube : (N ^ (τ / 3)) ^ 3 = N ^ τ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  calc (Real.log N + 1) ^ 3 ≤ ((3 / τ + 1) * N ^ (τ / 3)) ^ 3 :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hN]) hle 3
    _ = (3 / τ + 1) ^ 3 * N ^ τ := by rw [mul_pow, hcube]

/-- `log₂ 7 ≤ 250/89 ≤ 2.81`, because `7^89 ≤ 2^250`. -/
theorem logb_two_seven_le : Real.logb 2 7 ≤ 2.81 := by
  have h7 : Real.logb 2 7 ≤ 250 / 89 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    refine le_of_pow_le_pow_left₀ (n := 89) (by norm_num) (by positivity) ?_
    have h : (250 / 89 : ℝ) * ((89 : ℕ) : ℝ) = ((250 : ℕ) : ℝ) := by norm_num
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (250 / 89 : ℝ)) 89, ← Real.rpow_mul (by norm_num), h,
      Real.rpow_natCast]
    norm_num
  exact h7.trans (by norm_num)

/-- The sum of the bound of Theorem 17: with one call charged `CL (pre + wq)`, and the six products
bounded by multiples of `S` (the scans by a multiple of `κ S`), the time is a multiple of any `R`
with `S ≤ R` and `κ S ≤ R`. Here `rd` is the reading of the answers of one call and `sc`, `pr`,
`bd` are the three terms of the additional time. -/
theorem total_le {Tn N G Tdv pre wq rd sc pr bd C CL S R κ k1 k2 k3 k4 : ℝ}
    (h17 : Tn ≤ 4 * N * G * (Tdv + C * rd) + C * (sc + pr + bd))
    (hL : Tdv ≤ CL * (pre + wq)) (hB : 0 ≤ pre + wq) (hNG : 0 ≤ N * G) (hC : 0 ≤ C)
    (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2) (hk3 : 0 ≤ k3) (hk4 : 0 ≤ k4)
    (t1 : N * G * pre ≤ k1 * S) (t2 : N * G * wq ≤ k2 * S) (t3 : N * G * rd ≤ k3 * S)
    (t4 : sc ≤ κ * (k4 * S)) (t5 : pr ≤ S) (t6 : bd ≤ 2 * S) (hS : S ≤ R) (hκS : κ * S ≤ R) :
    Tn ≤ (4 * |CL| * k1 + 4 * |CL| * k2 + 4 * C * k3 + C * k4 + C + C * 2) * R := by
  have hA := abs_nonneg CL
  have hTd : Tdv ≤ |CL| * (pre + wq) :=
    hL.trans (mul_le_mul_of_nonneg_right (le_abs_self CL) hB)
  have s0 : 4 * N * G * (Tdv + C * rd) ≤ 4 * N * G * (|CL| * (pre + wq) + C * rd) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have b1 := mul_le_mul_of_nonneg_left t1 (by positivity : 0 ≤ 4 * |CL|)
  have b2 := mul_le_mul_of_nonneg_left t2 (by positivity : 0 ≤ 4 * |CL|)
  have b3 := mul_le_mul_of_nonneg_left t3 (by positivity : 0 ≤ 4 * C)
  have b4 := mul_le_mul_of_nonneg_left t4 hC
  have b5 := mul_le_mul_of_nonneg_left t5 hC
  have b6 := mul_le_mul_of_nonneg_left t6 hC
  have r1 := mul_le_mul_of_nonneg_left hS
    (by positivity : 0 ≤ 4 * |CL| * k1 + 4 * |CL| * k2 + 4 * C * k3 + C + C * 2)
  have r2 := mul_le_mul_of_nonneg_left hκS (by positivity : 0 ≤ C * k4)
  linarith

end ImprovedExponents
