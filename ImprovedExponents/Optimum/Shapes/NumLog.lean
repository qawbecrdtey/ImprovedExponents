module

public import ImprovedExponents.Optimum.Shapes.Crossing
public import ImprovedExponents.Optimum.GlobalLemmas

@[expose] public section

/-!
# Certified rational bounds for the saving of a general shape

The toolkit of `Optimum/NumLog.lean` for the functions of `Shapes/Defs.lean`. The two parameters
enter through `ln s` and `ln b`, which are enclosed by `logLo`/`logHi` at the integers `ks` and
`kb` (`2^ks` near `s`, `2^kb` near `b`); every other enclosure is as in `Optimum/NumLog.lean`,
and every rational side condition has the default proof `by numlog`. For rational `c`, `θ`, `r`
and numerals `s`, `b`:

* `gammaXS_le kx ks kb : γX(c, θ) ≤ r`, `le_gammaXS kx ks kb : r ≤ γX(c, θ)`, with `2^kx` near
  `c - 1`;
* `gammaQS_le k ks kb : γ_Q(θ) ≤ r`, `le_gammaQS k ks kb : r ≤ γ_Q(θ)`, with `2^k` near `θ`;
* `GamS_le hX hQ : Γ(c) ≤ r` and `le_GamS hX hQ : r ≤ Γ(c)` from the bounds at one `θ`;
* `basePrunedS_le k ks`, `le_basePrunedS k ks`, with `2^k` near `c`;
* `savingS_lt kb`, `lt_savingS kb`: bounds on `savingS b A γ` from bounds on `A` and `γ`;
* `shapeSaving_lt_of_mem_Icc kb`, `shapeSaving_lt_of_mem_Ioc kb`, `shapeSaving_lt_of_le kb`: the
  cells of a grid in `c`, the first cell `(c₀, c₂]` and the tail `[c₀, ∞)`, as in
  `Optimum/GlobalLemmas.lean`.

The generated files `Shapes/Cells_S*.lean` (by `python3 -m search.certs --encoding shapes`) use
these lemmas with the numerals of each shape, for example `shapeSaving 8 3 c` for the shape
`(2, 4)`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

/-! ### The enclosing functions -/

/-- A lower bound on `g2S s c δ`, written as
`-(c - 1) ln((c - 1 + δ)/(c - 1)) - δ ln(c - 1 + δ) - (1 - δ) ln(1 - δ) + δ ln s`;
`2^k` should be near `c - 1` and `2^ks` near `s`. -/
noncomputable def g2SLo (k ks : ℤ) (s : ℕ) (c δ : ℝ) : ℝ :=
  -(c - 1) * logHi 0 ((c - 1 + δ) / (c - 1)) - δ * logHi k (c - 1 + δ)
    - (1 - δ) * logHi 0 (1 - δ) + δ * logLo ks s

/-- An upper bound on `g2S s c δ`; `2^k` should be near `c - 1` and `2^ks` near `s`. -/
noncomputable def g2SHi (k ks : ℤ) (s : ℕ) (c δ : ℝ) : ℝ :=
  -(c - 1) * logLo 0 ((c - 1 + δ) / (c - 1)) - δ * logLo k (c - 1 + δ)
    - (1 - δ) * logLo 0 (1 - δ) + δ * logHi ks s

/-- Proves an equation or inequality between explicit rational numbers by evaluating both sides,
after unfolding the enclosing functions of this file and of `Optimum/NumLog.lean`. -/
macro "numlogS" : tactic =>
  `(tactic| norm_num [g2SLo, g2SHi, logLo, logHi, g2Lo, g2Hi, cEntLo, cEntHi, logApprox, logErr,
    seriesArg, logTwoLo, logTwoHi, logThreeLo, logThreeHi, logTenLo, logTenHi,
    Finset.sum_range_succ, rhoC])

/-! ### The exponent `γX` -/

/-- `g2SLo k ks s c δ ≤ g2S s c δ ≤ g2SHi k ks s c δ` for `s ≥ 1`, `c > 1` and `0 ≤ δ < 1`. -/
theorem g2S_mem (k ks : ℤ) {s : ℕ} {c δ : ℝ} (hs : 0 < s) (hc : 1 < c) (h0 : 0 ≤ δ)
    (h1 : δ < 1) : g2S s c δ ∈ Icc (g2SLo k ks s c δ) (g2SHi k ks s c δ) := by
  have hc1 : 0 < c - 1 := sub_pos.2 hc
  have hcδ : 0 < c - 1 + δ := by linarith
  have hδ1 : 0 < 1 - δ := sub_pos.2 h1
  have heq : g2S s c δ = -(c - 1) * log ((c - 1 + δ) / (c - 1)) - δ * log (c - 1 + δ)
      - (1 - δ) * log (1 - δ) + δ * log s := by
    rw [g2S, log_div hcδ.ne' hc1.ne']
    simp only [negMulLog]
    ring
  have hA := log_mem4 0 (div_pos hcδ hc1)
  have hB := log_mem4 k hcδ
  have hC := log_mem4 0 hδ1
  have hS := log_mem4 ks (by exact_mod_cast hs : (0 : ℝ) < s)
  rw [heq, g2SLo, g2SHi]
  constructor
  · linarith [mul_le_mul_of_nonneg_left hA.2 hc1.le, mul_le_mul_of_nonneg_left hB.2 h0,
      mul_le_mul_of_nonneg_left hC.2 hδ1.le, mul_le_mul_of_nonneg_left hS.1 h0]
  · linarith [mul_le_mul_of_nonneg_left hA.1 hc1.le, mul_le_mul_of_nonneg_left hB.1 h0,
      mul_le_mul_of_nonneg_left hC.1 hδ1.le, mul_le_mul_of_nonneg_left hS.2 h0]

/-- An upper bound `γX(c, θ) ≤ r` at rational arguments; `2^kx` near `c - 1`, `2^ks` near `s`,
`2^kb` near `b`. -/
theorem gammaXS_le (kx ks kb : ℤ) {s b : ℕ} {c θ r : ℝ} (hs : 0 < s := by norm_num)
    (hb : 2 ≤ b := by norm_num) (hc : 1 < c := by numlogS) (h0 : 0 ≤ θ := by numlogS)
    (h1 : θ < 1 := by numlogS) (hr : 0 ≤ r := by numlogS)
    (h : -g2SLo kx ks s c θ ≤ r * logLo kb b := by numlogS) : gammaXS s b c θ ≤ r := by
  have hlb := logS_pos hb
  rw [gammaXS, div_le_iff₀ hlb]
  linarith [(g2S_mem kx ks hs hc h0 h1).1,
    mul_le_mul_of_nonneg_left (log_mem4 kb (by positivity : (0 : ℝ) < b)).1 hr]

/-- A lower bound `r ≤ γX(c, θ)` at rational arguments; `2^kx` near `c - 1`, `2^ks` near `s`,
`2^kb` near `b`. -/
theorem le_gammaXS (kx ks kb : ℤ) {s b : ℕ} {c θ r : ℝ} (hs : 0 < s := by norm_num)
    (hb : 2 ≤ b := by norm_num) (hc : 1 < c := by numlogS) (h0 : 0 ≤ θ := by numlogS)
    (h1 : θ < 1 := by numlogS) (hr : 0 ≤ r := by numlogS)
    (h : r * logHi kb b ≤ -g2SHi kx ks s c θ := by numlogS) : r ≤ gammaXS s b c θ := by
  have hlb := logS_pos hb
  rw [gammaXS, le_div_iff₀ hlb]
  linarith [(g2S_mem kx ks hs hc h0 h1).2,
    mul_le_mul_of_nonneg_left (log_mem4 kb (by positivity : (0 : ℝ) < b)).2 hr]

/-! ### The exponent `γ_Q` -/

/-- `(H(θ) + θ ln s)/ln b ≥ r'` from `r' ln b ≤ H(θ) + θ ln s`, with `H(θ)` written out. -/
theorem le_qS (k ks kb : ℤ) {s b : ℕ} {θ r : ℝ} (hs : 0 < s) (hb : 2 ≤ b) (h0 : 0 < θ)
    (h1 : θ < 1) (hr : 0 ≤ r)
    (h : r * logHi kb b ≤ -θ * logHi k θ - (1 - θ) * logHi 0 (1 - θ) + θ * logLo ks s) :
    r ≤ qS s b θ := by
  have hlb := logS_pos hb
  have hT := log_mem4 k h0
  have hU := log_mem4 0 (sub_pos.2 h1)
  have hS := log_mem4 ks (by exact_mod_cast hs : (0 : ℝ) < s)
  have hB := log_mem4 kb (by positivity : (0 : ℝ) < b)
  rw [qS, entropy, le_div_iff₀ hlb]
  nlinarith [mul_le_mul_of_nonneg_left hT.2 h0.le, mul_le_mul_of_nonneg_left hU.2 (sub_pos.2 h1).le,
    mul_le_mul_of_nonneg_left hS.1 h0.le, mul_le_mul_of_nonneg_left hB.2 hr]

/-- `(H(θ) + θ ln s)/ln b ≤ r'` from `H(θ) + θ ln s ≤ r' ln b`, with `H(θ)` written out. -/
theorem qS_le (k ks kb : ℤ) {s b : ℕ} {θ r : ℝ} (hs : 0 < s) (hb : 2 ≤ b) (h0 : 0 < θ)
    (h1 : θ < 1) (hr : 0 ≤ r)
    (h : -θ * logLo k θ - (1 - θ) * logLo 0 (1 - θ) + θ * logHi ks s ≤ r * logLo kb b) :
    qS s b θ ≤ r := by
  have hlb := logS_pos hb
  have hT := log_mem4 k h0
  have hU := log_mem4 0 (sub_pos.2 h1)
  have hS := log_mem4 ks (by exact_mod_cast hs : (0 : ℝ) < s)
  have hB := log_mem4 kb (by positivity : (0 : ℝ) < b)
  rw [qS, entropy, div_le_iff₀ hlb]
  nlinarith [mul_le_mul_of_nonneg_left hT.1 h0.le, mul_le_mul_of_nonneg_left hU.1 (sub_pos.2 h1).le,
    mul_le_mul_of_nonneg_left hS.2 h0.le, mul_le_mul_of_nonneg_left hB.1 hr]

/-- An upper bound `γ_Q(θ) ≤ r` at a rational `θ`; `2^k` near `θ`, `2^ks` near `s`, `2^kb` near
`b`. It needs `r ≤ 2/3`. -/
theorem gammaQS_le (k ks kb : ℤ) {s b : ℕ} {θ r : ℝ} (hs : 0 < s := by norm_num)
    (hb : 2 ≤ b := by norm_num) (h0 : 0 < θ := by numlogS) (h1 : θ < 1 := by numlogS)
    (hr : 0 ≤ (2 - 3 * r) / 4 := by numlogS)
    (h : (2 - 3 * r) / 4 * logHi kb b
      ≤ -θ * logHi k θ - (1 - θ) * logHi 0 (1 - θ) + θ * logLo ks s := by numlogS) :
    gammaQS s b θ ≤ r := by
  have hq := le_qS k ks kb hs hb h0 h1 hr h
  unfold gammaQS
  linarith

/-- A lower bound `r ≤ γ_Q(θ)` at a rational `θ`; `2^k` near `θ`, `2^ks` near `s`, `2^kb` near
`b`. It needs `r ≤ 2/3`. -/
theorem le_gammaQS (k ks kb : ℤ) {s b : ℕ} {θ r : ℝ} (hs : 0 < s := by norm_num)
    (hb : 2 ≤ b := by norm_num) (h0 : 0 < θ := by numlogS) (h1 : θ < 1 := by numlogS)
    (hr : 0 ≤ (2 - 3 * r) / 4 := by numlogS)
    (h : -θ * logLo k θ - (1 - θ) * logLo 0 (1 - θ) + θ * logHi ks s
      ≤ (2 - 3 * r) / 4 * logLo kb b := by numlogS) : r ≤ gammaQS s b θ := by
  have hq := qS_le k ks kb hs hb h0 h1 hr h
  unfold gammaQS
  linarith

/-! ### The exponent `Γ` -/

/-- A lower bound on `Γ(c)` from lower bounds on `γX(c, θ)` and `γ_Q(θ)` at one `θ`. -/
theorem le_GamS {s b : ℕ} {c θ r : ℝ} (hX : r ≤ gammaXS s b c θ) (hQ : r ≤ gammaQS s b θ)
    (hs : 0 < s := by norm_num) (hb : 2 ≤ b := by norm_num) (hsb : b < (s + 1) ^ 2 := by norm_num)
    (hc : (s : ℝ) + 1 < c := by numlogS) (h0 : 0 < θ := by numlogS)
    (h9 : θ < (s : ℝ) / (s + 1) := by numlogS) : r ≤ GamS s b c :=
  (le_min hX hQ).trans (GamS_ge_min hb hs hsb hc ⟨h0, h9⟩)

/-- An upper bound on `Γ(c)` from upper bounds on `γX(c, θ)` and `γ_Q(θ)` at one `θ`. -/
theorem GamS_le {s b : ℕ} {c θ r : ℝ} (hX : gammaXS s b c θ ≤ r) (hQ : gammaQS s b θ ≤ r)
    (hs : 0 < s := by norm_num) (hb : 2 ≤ b := by norm_num) (hsb : b < (s + 1) ^ 2 := by norm_num)
    (hc : (s : ℝ) + 1 < c := by numlogS) (h0 : 0 < θ := by numlogS)
    (h9 : θ < (s : ℝ) / (s + 1) := by numlogS) : GamS s b c ≤ r :=
  (GamS_le_max hb hs hsb hc ⟨h0, h9⟩).trans (max_le hX hQ)

/-! ### The thinness constant -/

/-- An upper bound `basePrunedS s c ≤ r` at a rational `c`; `2^k` near `c`, `2^ks` near `s`. -/
theorem basePrunedS_le (k ks : ℤ) {s : ℕ} {c r : ℝ} (hs : 0 < s := by norm_num)
    (hc : 1 < c := by numlogS)
    (h : 1 / 2 * cEntHi k c + (c - 1) * logHi ks s / 2 ≤ r := by numlogS) :
    basePrunedS s c ≤ r := by
  rw [basePrunedS_eq hc]
  have hS := log_mem4 ks (by exact_mod_cast hs : (0 : ℝ) < s)
  linarith [(cEntropy_mem k hc).2, mul_le_mul_of_nonneg_left hS.2 (sub_pos.2 hc).le]

/-- A lower bound `r ≤ basePrunedS s c` at a rational `c`; `2^k` near `c`, `2^ks` near `s`. -/
theorem le_basePrunedS (k ks : ℤ) {s : ℕ} {c r : ℝ} (hs : 0 < s := by norm_num)
    (hc : 1 < c := by numlogS)
    (h : r ≤ 1 / 2 * cEntLo k c + (c - 1) * logLo ks s / 2 := by numlogS) :
    r ≤ basePrunedS s c := by
  rw [basePrunedS_eq hc]
  have hS := log_mem4 ks (by exact_mod_cast hs : (0 : ℝ) < s)
  linarith [(cEntropy_mem k hc).1, mul_le_mul_of_nonneg_left hS.1 (sub_pos.2 hc).le]

/-! ### The saving -/

/-- The denominator `A + γ ln b` is positive for `A > 0`, `γ ≥ 0` and `b ≥ 2`. -/
theorem thinRS_den_pos {b : ℕ} {A γ : ℝ} (hb : 2 ≤ b) (hA : 0 < A) (hγ : 0 ≤ γ) :
    0 < A + γ * log b :=
  add_pos_of_pos_of_nonneg hA (mul_nonneg hγ (logS_pos hb).le)

/-- `savingS b A γ = γ ln b/(2 (A + γ ln b))`. -/
theorem savingS_eq_div (b : ℕ) (A γ : ℝ) :
    savingS b A γ = γ * log b / (2 * (A + γ * log b)) := by
  rw [savingS, thinRS, div_mul_eq_mul_div, div_div, mul_comm (log (b : ℝ)) γ,
    mul_comm (A + γ * log (b : ℝ)) 2]

/-- An upper bound `savingS b A γ < u` from a lower bound `Alo ≤ A` and an upper bound `γ ≤ γhi`;
`2^kb` near `b`. -/
theorem savingS_lt (kb : ℤ) {b : ℕ} {A γ Alo γhi u : ℝ} (hA : Alo ≤ A) (hγ0 : 0 ≤ γ)
    (hγ : γ ≤ γhi) (hb : 2 ≤ b := by norm_num) (hAlo : 0 < Alo := by numlogS)
    (hu0 : 0 ≤ u := by numlogS) (hu : u ≤ 1 / 2 := by numlogS)
    (h : γhi * (1 - 2 * u) * logHi kb b < 2 * u * Alo := by numlogS) : savingS b A γ < u := by
  have hlb := logS_pos hb
  have hB := log_mem4 kb (by positivity : (0 : ℝ) < b)
  have h1 : γ * (1 - 2 * u) * log b ≤ γhi * (1 - 2 * u) * logHi kb b :=
    mul_le_mul (mul_le_mul_of_nonneg_right hγ (by linarith)) hB.2 hlb.le
      (mul_nonneg (hγ0.trans hγ) (by linarith))
  have h2 : 2 * u * Alo ≤ 2 * u * A := mul_le_mul_of_nonneg_left hA (by linarith)
  rw [savingS_eq_div, div_lt_iff₀ (mul_pos two_pos (thinRS_den_pos hb (hAlo.trans_le hA) hγ0))]
  linarith

/-- A lower bound `u < savingS b A γ` from an upper bound `A ≤ Ahi` and a lower bound `γlo ≤ γ`;
`2^kb` near `b`. -/
theorem lt_savingS (kb : ℤ) {b : ℕ} {A γ Ahi γlo u : ℝ} (hA : 0 < A) (hAhi : A ≤ Ahi)
    (hγ : γlo ≤ γ) (hb : 2 ≤ b := by norm_num) (hγlo : 0 ≤ γlo := by numlogS)
    (hu0 : 0 ≤ u := by numlogS) (hu : u ≤ 1 / 2 := by numlogS)
    (h : 2 * u * Ahi < γlo * (1 - 2 * u) * logLo kb b := by numlogS) : u < savingS b A γ := by
  have hlb := logS_pos hb
  have hB := log_mem4 kb (by positivity : (0 : ℝ) < b)
  have hγ0 := hγlo.trans hγ
  have hlo : 0 ≤ logLo kb b := by
    by_contra hneg
    have h3 : γlo * (1 - 2 * u) * logLo kb b ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hγlo (by linarith)) (not_le.1 hneg).le
    linarith [mul_nonneg (mul_nonneg two_pos.le hu0) (hA.trans_le hAhi).le]
  have h1 : γlo * (1 - 2 * u) * logLo kb b ≤ γ * (1 - 2 * u) * log b :=
    mul_le_mul (mul_le_mul_of_nonneg_right hγ (by linarith)) hB.1 hlo
      (mul_nonneg hγ0 (by linarith))
  have h2 : 2 * u * A ≤ 2 * u * Ahi := mul_le_mul_of_nonneg_left hAhi (by linarith)
  rw [savingS_eq_div, lt_div_iff₀ (mul_pos two_pos (thinRS_den_pos hb hA hγ0))]
  linarith

/-! ### The cells of a grid in `c` -/

/-- A cell of a grid in `c`: `shapeSaving s b c < u` for all `c₁ ≤ c ≤ c₂`, from
`Alo ≤ basePrunedS s c₁` and `Γ(c₂) ≤ γhi`; `2^kb` near `b`. -/
theorem shapeSaving_lt_of_mem_Icc (kb : ℤ) {s b : ℕ} {c₁ c₂ c Alo γhi u : ℝ}
    (hA : Alo ≤ basePrunedS s c₁) (hγ : GamS s b c₂ ≤ γhi) (hc : c ∈ Icc c₁ c₂)
    (hs : 0 < s := by norm_num) (hb : 2 ≤ b := by norm_num) (hsb : b < (s + 1) ^ 2 := by norm_num)
    (hc₁ : (s : ℝ) + 1 < c₁ := by numlogS) (hAlo : 0 < Alo := by numlogS)
    (hu0 : 0 ≤ u := by numlogS) (hu : u ≤ 1 / 2 := by numlogS)
    (h : γhi * (1 - 2 * u) * logHi kb b < 2 * u * Alo := by numlogS) : shapeSaving s b c < u := by
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hcs : (s : ℝ) + 1 < c := hc₁.trans_le hc.1
  have hmono : basePrunedS s c₁ ≤ basePrunedS s c :=
    basePrunedS_monotoneOn hs (by simp only [mem_Ioi]; linarith) (by simp only [mem_Ioi]; linarith)
      hc.1
  exact savingS_lt kb (hA.trans hmono) (GamS_pos hb hs hsb hcs).le
    ((GamS_monotoneOn hb hs hsb hcs (hcs.trans_le hc.2) hc.2).trans hγ) hb hAlo hu0 hu h

/-- The first cell of a grid in `c`: `shapeSaving s b c < u` for all `c₀ < c ≤ c₂`, from
`Alo ≤ basePrunedS s c₀` with `c₀ ≥ s + 1` and `Γ(c₂) ≤ γhi`; `2^kb` near `b`. -/
theorem shapeSaving_lt_of_mem_Ioc (kb : ℤ) {s b : ℕ} {c₀ c₂ c Alo γhi u : ℝ}
    (hA : Alo ≤ basePrunedS s c₀) (hγ : GamS s b c₂ ≤ γhi) (hc : c ∈ Ioc c₀ c₂)
    (hs : 0 < s := by norm_num) (hb : 2 ≤ b := by norm_num) (hsb : b < (s + 1) ^ 2 := by norm_num)
    (hc₀ : (s : ℝ) + 1 ≤ c₀ := by numlogS) (hAlo : 0 < Alo := by numlogS)
    (hu0 : 0 ≤ u := by numlogS) (hu : u ≤ 1 / 2 := by numlogS)
    (h : γhi * (1 - 2 * u) * logHi kb b < 2 * u * Alo := by numlogS) : shapeSaving s b c < u := by
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hcs : (s : ℝ) + 1 < c := hc₀.trans_lt hc.1
  have hmono : basePrunedS s c₀ ≤ basePrunedS s c :=
    basePrunedS_monotoneOn hs (by simp only [mem_Ioi]; linarith) (by simp only [mem_Ioi]; linarith)
      hc.1.le
  exact savingS_lt kb (hA.trans hmono) (GamS_pos hb hs hsb hcs).le
    ((GamS_monotoneOn hb hs hsb hcs (hcs.trans_le hc.2) hc.2).trans hγ) hb hAlo hu0 hu h

/-- The tail of a grid in `c`: `shapeSaving s b c < u` for all `c ≥ c₀`, from
`Alo ≤ basePrunedS s c₀` and `Γ(c) < 2/3`; `2^kb` near `b`. -/
theorem shapeSaving_lt_of_le (kb : ℤ) {s b : ℕ} {c₀ c Alo u : ℝ} (hA : Alo ≤ basePrunedS s c₀)
    (hc : c₀ ≤ c) (hs : 0 < s := by norm_num) (hb : 2 ≤ b := by norm_num)
    (hsb : b < (s + 1) ^ 2 := by norm_num) (hc₀ : (s : ℝ) + 1 < c₀ := by numlogS)
    (hAlo : 0 < Alo := by numlogS) (hu0 : 0 ≤ u := by numlogS) (hu : u ≤ 1 / 2 := by numlogS)
    (h : 2 / 3 * (1 - 2 * u) * logHi kb b < 2 * u * Alo := by numlogS) : shapeSaving s b c < u := by
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hcs : (s : ℝ) + 1 < c := hc₀.trans_le hc
  have hmono : basePrunedS s c₀ ≤ basePrunedS s c :=
    basePrunedS_monotoneOn hs (by simp only [mem_Ioi]; linarith) (by simp only [mem_Ioi]; linarith)
      hc
  exact savingS_lt kb (hA.trans hmono) (GamS_pos hb hs hsb hcs).le
    (GamS_lt_two_thirds hb hs hsb hcs).le hb hAlo hu0 hu h

end ImprovedExponents
