module

public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters

@[expose] public section

/-!
# The parameters of Theorem 17 at rational exponents

Upstream instantiates the reduction of Theorem 17 with `D := ⌊n^{1/18}⌋` and `g := ⌈D^{0.0315}⌉`
(and with one more choice).  Here the exponents are arbitrary rational numbers `a/b` and `c/d`:

* `paramDRat a b n = ⌊n^{a/b}⌋` and `paramGRat c d D = ⌈D^{c/d}⌉`, with real powers;
  `paramGRatOf a b c d n = paramGRat c d (paramDRat a b n)` is `g` as a function of `n`, which is
  the form in which `Claim.Theorem_17` takes it.
* `paramDRatNat a b n = rootFloor b (n^a)` and `paramGRatNat c d D = rootCeil d (D^c)` are the same
  numbers in integer arithmetic (`paramDRatNat_eq`, for `b ≥ 1`; `paramGRatNat_eq`, for `d ≥ 1` and
  `D ≥ 1`).  A program finds them by counting up.
* Bounds: `paramDRatNat a b n ≤ n^a` and `paramGRatNat c d D ≤ D^c + 1` always; and
  `paramDRatNat a b n ≤ n^k` if `a ≤ k b`, `paramGRatNat c d D ≤ D^k` if `c ≤ k d`, for `n ≥ 1`,
  `D ≥ 1` (`paramDRatNat_le_pow`, `paramGRatNat_le_pow`).
* The hypotheses `D ≤ n` and `g ≥ 1` of Theorem 17 hold for `a ≤ b` and `n ≥ 1`
  (`paramDRat_le_self`, `one_le_paramGRatOf`).
* For `c = 0` the parameter `g` is 1 (`paramGRat_zero`, `paramGRatNat_zero`).
* Upstream's second choice is the case `a/b = 1/18`, `c/d = 63/2000` (`paramDRat_one_eighteen`,
  `paramGRatOf_eq_paramG₂₆`).
-/

namespace ImprovedExponents.ParamRoutines

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The parameters, with real powers -/

/-- `D := ⌊n^{a/b}⌋`. -/
noncomputable def paramDRat (a b n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((a : ℝ) / b)⌋₊

/-- `g := ⌈D^{c/d}⌉`, as a function of `D`. -/
noncomputable def paramGRat (c d D : ℕ) : ℕ := ⌈(D : ℝ) ^ ((c : ℝ) / d)⌉₊

/-- `g := ⌈D^{c/d}⌉` for `D := ⌊n^{a/b}⌋`, as a function of `n`. -/
noncomputable def paramGRatOf (a b c d n : ℕ) : ℕ := paramGRat c d (paramDRat a b n)

/-! ## The parameters, in integer arithmetic -/

/-- `⌊n^{a/b}⌋`: the greatest `x` with `x^b ≤ n^a`. -/
def paramDRatNat (a b n : ℕ) : ℕ := rootFloor b (n ^ a)

/-- `⌈D^{c/d}⌉`: the least `g` with `g^d ≥ D^c`. -/
def paramGRatNat (c d D : ℕ) : ℕ := rootCeil d (D ^ c)

/-- `n^{a/b}` is the `b`-th root of `n^a`. -/
theorem rpow_natCast_div (n a b : ℕ) :
    (n : ℝ) ^ ((a : ℝ) / b) = ((n ^ a : ℕ) : ℝ) ^ ((b : ℝ)⁻¹) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul n.cast_nonneg, div_eq_mul_inv]

/-- `rootFloor b (n^a)` is `⌊n^{a/b}⌋`. -/
theorem paramDRatNat_eq {b : ℕ} (hb : b ≠ 0) (a n : ℕ) : paramDRatNat a b n = paramDRat a b n := by
  rw [paramDRatNat, paramDRat, rpow_natCast_div, floor_rpow_inv hb]

/-- `rootCeil d (D^c)` is `⌈D^{c/d}⌉`, for `D ≥ 1`. -/
theorem paramGRatNat_eq {d : ℕ} (hd : d ≠ 0) (c : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    paramGRatNat c d D = paramGRat c d D := by
  rw [paramGRatNat, paramGRat, rpow_natCast_div, ceil_rpow_inv hd (Nat.one_le_pow _ _ hD)]

/-- `⌈D^{c/d}⌉` for `D = ⌊n^{a/b}⌋`, as the claim of Theorem 17 takes it. -/
theorem paramGRatNat_paramDRat {d : ℕ} (hd : d ≠ 0) (a b c : ℕ) {n : ℕ}
    (hD : 1 ≤ paramDRat a b n) :
    paramGRatNat c d (paramDRat a b n) = paramGRatOf a b c d n :=
  paramGRatNat_eq hd c hD

/-! ## Bounds -/

/-- `⌊n^{a/b}⌋ ≥ 1` for `n ≥ 1`. -/
theorem one_le_paramDRatNat {b : ℕ} (hb : b ≠ 0) (a : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ paramDRatNat a b n :=
  le_rootFloor hb (by simpa using Nat.one_le_pow a n hn)

/-- `⌊n^{a/b}⌋ ≥ 1` for `n ≥ 1`, with the real power. -/
theorem one_le_paramDRat {b : ℕ} (hb : b ≠ 0) (a : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ paramDRat a b n :=
  paramDRatNat_eq hb a n ▸ one_le_paramDRatNat hb a hn

/-- `⌈D^{c/d}⌉ ≥ 1`. -/
theorem one_le_paramGRatNat (c d D : ℕ) : 1 ≤ paramGRatNat c d D := Nat.succ_le_succ (Nat.zero_le _)

/-- `⌊n^{a/b}⌋ ≤ n^a`, whatever `b` is. -/
theorem paramDRatNat_le (a b n : ℕ) : paramDRatNat a b n ≤ n ^ a := Nat.findGreatest_le _

/-- `⌈D^{c/d}⌉ ≤ D^c + 1`, whatever `d` and `D` are. -/
theorem paramGRatNat_le (c d D : ℕ) : paramGRatNat c d D ≤ D ^ c + 1 :=
  Nat.succ_le_succ (Nat.findGreatest_le _)

/-- `⌊n^{a/b}⌋ ≤ n^k` if `a/b ≤ k`, for `n ≥ 1`. -/
theorem paramDRatNat_le_pow {a b k : ℕ} (hb : b ≠ 0) (h : a ≤ k * b) {n : ℕ} (hn : 1 ≤ n) :
    paramDRatNat a b n ≤ n ^ k := by
  refine (Nat.pow_le_pow_iff_left hb).1 ((rootFloor_pow_le hb _).trans ?_)
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hn h

/-- `⌈D^{c/d}⌉ ≤ D^k` if `c/d ≤ k`, for `D ≥ 1`. -/
theorem paramGRatNat_le_pow {c d k : ℕ} (hd : d ≠ 0) (h : c ≤ k * d) {D : ℕ} (hD : 1 ≤ D) :
    paramGRatNat c d D ≤ D ^ k := by
  refine rootCeil_le hd (Nat.one_le_pow _ _ hD) ?_
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hD h

/-- `⌊n^{a/b}⌋ ≤ n` if `a ≤ b`, for `n ≥ 1`: the hypothesis `D ≤ n` of Theorem 17. -/
theorem paramDRat_le_self {a b : ℕ} (hb : b ≠ 0) (hab : a ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    paramDRat a b n ≤ n := by
  simpa [paramDRatNat_eq hb] using paramDRatNat_le_pow (k := 1) hb (by omega) hn

/-- `⌈D^{c/d}⌉ ≥ 1` for `D = ⌊n^{a/b}⌋` and `n ≥ 1`: the hypothesis `g ≥ 1` of Theorem 17. -/
theorem one_le_paramGRatOf {b d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) (a c : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ paramGRatOf a b c d n :=
  paramGRatNat_paramDRat hd a b c (one_le_paramDRat hb a hn) ▸ one_le_paramGRatNat c d _

/-! ## The exponent zero -/

/-- For `c = 0`, `g = 1`. -/
theorem paramGRat_zero (d D : ℕ) : paramGRat 0 d D = 1 := by simp [paramGRat]

/-- For `c = 0`, `g = 1`, in integer arithmetic. -/
theorem paramGRatNat_zero {d : ℕ} (hd : d ≠ 0) (D : ℕ) : paramGRatNat 0 d D = 1 :=
  le_antisymm (by simpa [paramGRatNat] using rootCeil_le (g := 1) hd (le_refl 1) (by simp))
    (one_le_paramGRatNat 0 d D)

/-! ## Upstream's choice -/

/-- Upstream's "D := ⌊n^{1/18}⌋" is the case `a/b = 1/18`. -/
theorem paramDRat_one_eighteen : paramDRat 1 18 = paramD₂₆ := by
  funext n
  simp [paramDRat, paramD₂₆]

/-- Upstream's "g := ⌈D^{0.0315}⌉" is the case `c/d = 63/2000`, as a function of `D`. -/
theorem paramGRat_sixtyThree (D : ℕ) : paramGRat 63 2000 D = ⌈(D : ℝ) ^ (0.0315 : ℝ)⌉₊ := by
  rw [paramGRat]
  norm_num

/-- Upstream's "g := ⌈D^{0.0315}⌉" for "D := ⌊n^{1/18}⌋" is the case `a/b = 1/18`,
`c/d = 63/2000`. -/
theorem paramGRatOf_eq_paramG₂₆ : paramGRatOf 1 18 63 2000 = paramG₂₆ := by
  funext n
  rw [paramGRatOf, paramGRat_sixtyThree, paramDRat_one_eighteen, paramG₂₆]

end ImprovedExponents.ParamRoutines
