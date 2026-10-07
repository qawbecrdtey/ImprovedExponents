module

public import ImprovedExponents.Optimum.Shapes.Defs
public import ImprovedExponents.Optimum.PerCCrossing

@[expose] public section

/-!
# The crossing point of `γX` and `γ_Q` for a general shape

The analysis of `Optimum/PerCBasic.lean`, `Optimum/PerCCrossing.lean` and `ExactCount/G2.lean`
for the functions of `Shapes/Defs.lean`, with the parameters `s` (outer outputs) and `b` (inner
length). The hypotheses are `2 ≤ b`, `0 < s` (or `2 ≤ s`), `b < (s + 1)²` and `s + 1 < c`.

* `g2S s c` decreases strictly on `[0, 1]` for `c > s + 1`: its derivative is
  `ln(s (1 - δ)/(c - 1 + δ)) < 0` (`g2S_strictAntiOn_right`); so `γX(c, ·)` increases strictly
  from `γX(c, 0) = 0` (`gammaXS_strictMonoOn`, `gammaXS_pos`), and `γX(·, θ)` is nondecreasing
  (`gammaXS_monotoneOn`).
* `q` increases strictly on `[0, s/(s+1)]`, where its derivative is `ln(s (1 - θ)/θ)/ln b > 0`
  (`qS_strictMonoOn`), from `q(0) = 0` to `q(s/(s+1)) = log_b(s + 1)` (`qS_zero`,
  `qS_at_right`), which exceeds `1/2` exactly when `b < (s + 1)²`; so `γ_Q` decreases strictly
  from `2/3` to a negative value (`gammaQS_strictAntiOn`, `gammaQS_neg_at_right`).
* Hence `γX(c, ·)` and `γ_Q` cross at exactly one `θ* ∈ (0, s/(s+1))`, where `Γ(c)` is their common
  value (`exists_crossingS`, `GamS_eq_of_crossing`), `0 < Γ(c) < 2/3` (`GamS_pos`,
  `GamS_lt_two_thirds`), `min ≤ Γ(c) ≤ max` at every `θ₀` (`GamS_ge_min`, `GamS_le_max`), and
  `Γ` is nondecreasing in `c` (`GamS_monotoneOn`).
* The thinness constant `basePrunedS s` is positive and nondecreasing on `(1, ∞)`: its derivative
  is `(ln s)/2 - (1/2) ln(1 - 1/c) > 0` (`basePrunedS_pos`, `basePrunedS_monotoneOn`).
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

variable {s b : ℕ} {c θ θ₀ : ℝ}

/-! ### The parameters -/

/-- `ln b > 0` for `b ≥ 2`. -/
theorem logS_pos (hb : 2 ≤ b) : 0 < log (b : ℝ) :=
  log_pos (by exact_mod_cast hb)

/-- `ln s ≥ 0` for `s ≥ 1`. -/
theorem logS_nonneg (hs : 0 < s) : 0 ≤ log (s : ℝ) :=
  log_nonneg (by exact_mod_cast hs)

/-- `0 < s/(s+1)` for `s ≥ 1`. -/
theorem window_pos (hs : 0 < s) : (0 : ℝ) < s / (s + 1) :=
  div_pos (by exact_mod_cast hs) (by positivity)

/-- `s/(s+1) < 1`. -/
theorem window_lt_one : (s : ℝ) / (s + 1) < 1 :=
  (div_lt_one (by positivity)).2 (by linarith)

/-! ### The exponent `g₂` -/

@[simp] theorem g2S_zero (c : ℝ) : g2S s c 0 = 0 := by simp [g2S]

/-- `g₂(c, ·)` is continuous. -/
theorem continuous_g2S_right (c : ℝ) : Continuous (g2S s c) := by
  unfold g2S
  fun_prop

/-- `g₂(·, δ)` is continuous. -/
theorem continuous_g2S_left (δ : ℝ) : Continuous fun c => g2S s c δ := by
  unfold g2S
  fun_prop

/-- `∂g₂/∂δ = ln(s (1 - δ)/(c - 1 + δ))`. -/
theorem hasDerivAt_g2S_right {δ : ℝ} (hs : 0 < s) (hc : 1 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    HasDerivAt (g2S s c) (log (s * (1 - δ) / (c - 1 + δ))) δ := by
  have hpos : 0 < c - 1 + δ := by linarith
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 : HasDerivAt (fun δ : ℝ => negMulLog (c - 1 + δ)) ((-log (c - 1 + δ) - 1) * 1) δ :=
    (hasDerivAt_negMulLog hpos.ne').comp δ ((hasDerivAt_id δ).const_add (c - 1))
  have h2 : HasDerivAt (fun δ : ℝ => negMulLog (1 - δ)) ((-log (1 - δ) - 1) * (-1)) δ :=
    (hasDerivAt_negMulLog (sub_pos.2 hδ1).ne').comp δ ((hasDerivAt_id δ).const_sub 1)
  have h3 : HasDerivAt (fun δ : ℝ => δ * log s) (1 * log s) δ :=
    (hasDerivAt_id δ).mul_const (log s)
  have h : HasDerivAt (g2S s c) _ δ := ((h1.sub_const (negMulLog (c - 1))).add h2).add h3
  refine h.congr_deriv ?_
  rw [log_div (by positivity) hpos.ne', log_mul hs'.ne' (sub_pos.2 hδ1).ne']
  ring

/-- `∂g₂/∂c = ln((c - 1)/(c - 1 + δ))`. -/
theorem hasDerivAt_g2S_left {δ : ℝ} (hc : 1 < c) (hδ : 0 ≤ δ) :
    HasDerivAt (fun c => g2S s c δ) (log ((c - 1) / (c - 1 + δ))) c := by
  have hpos : 0 < c - 1 + δ := by linarith
  have h1 : HasDerivAt (negMulLog ∘ fun c : ℝ => c - 1 + δ) ((-log (c - 1 + δ) - 1) * 1) c :=
    (hasDerivAt_negMulLog hpos.ne').comp c (((hasDerivAt_id c).sub_const 1).add_const δ)
  have h2 : HasDerivAt (negMulLog ∘ fun c : ℝ => c - 1) ((-log (c - 1) - 1) * 1) c :=
    (hasDerivAt_negMulLog (sub_pos.2 hc).ne').comp c ((hasDerivAt_id c).sub_const 1)
  have h : HasDerivAt (fun c => g2S s c δ) _ c :=
    ((h1.sub h2).add_const (negMulLog (1 - δ))).add_const (δ * log s)
  refine h.congr_deriv ?_
  rw [log_div (sub_pos.2 hc).ne' hpos.ne']
  ring

/-- `g₂(c, ·)` decreases strictly on `[0, 1]` when `c > s + 1`: its derivative
`ln(s (1 - δ)/(c - 1 + δ))` is negative. -/
theorem g2S_strictAntiOn_right (hs : 0 < s) (hc : (s : ℝ) + 1 < c) :
    StrictAntiOn (g2S s c) (Icc 0 1) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  refine strictAntiOn_of_deriv_neg (convex_Icc 0 1) (continuous_g2S_right c).continuousOn ?_
  intro δ hδ
  rw [interior_Icc] at hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  rw [(hasDerivAt_g2S_right hs (by linarith) hδ0 hδ1).deriv]
  have hpos : 0 < c - 1 + δ := by linarith
  refine log_neg (div_pos (by nlinarith) hpos) ?_
  rw [div_lt_one hpos]
  nlinarith

/-- `g₂(·, δ)` decreases on `[1, ∞)` for `δ ≥ 0`: its derivative is
`ln((c - 1)/(c - 1 + δ)) ≤ 0`. -/
theorem g2S_antitoneOn_left {δ : ℝ} (hδ : 0 ≤ δ) : AntitoneOn (fun c => g2S s c δ) (Ici 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 1) (continuous_g2S_left δ).continuousOn ?_ ?_
  · intro c hc
    rw [interior_Ici] at hc
    exact (hasDerivAt_g2S_left hc hδ).differentiableAt.differentiableWithinAt
  · intro c hc
    rw [interior_Ici] at hc
    have hc' : 1 < c := hc
    rw [(hasDerivAt_g2S_left hc' hδ).deriv]
    have hpos : 0 < c - 1 + δ := by linarith
    refine log_nonpos (div_nonneg (by linarith) hpos.le) ?_
    rw [div_le_one hpos]
    linarith

/-- `g₂(c, δ) < 0` for `c > s + 1` and `0 < δ ≤ 1`. -/
theorem g2S_neg {δ : ℝ} (hs : 0 < s) (hc : (s : ℝ) + 1 < c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    g2S s c δ < 0 := by
  have h := g2S_strictAntiOn_right hs hc (left_mem_Icc.2 zero_le_one) ⟨hδ0.le, hδ1⟩ hδ0
  rwa [g2S_zero] at h

/-! ### The exponent `γX` -/

@[simp] theorem gammaXS_zero (c : ℝ) : gammaXS s b c 0 = 0 := by simp [gammaXS]

/-- `γX(c, ·)` is continuous. -/
theorem continuous_gammaXS_right (c : ℝ) : Continuous (gammaXS s b c) :=
  (continuous_g2S_right c).neg.div_const _

/-- `γX(c, θ) > 0` for `c > s + 1` and `0 < θ ≤ 1`. -/
theorem gammaXS_pos (hb : 2 ≤ b) (hs : 0 < s) (hc : (s : ℝ) + 1 < c) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) : 0 < gammaXS s b c θ :=
  div_pos (neg_pos.2 (g2S_neg hs hc hθ0 hθ1)) (logS_pos hb)

/-- `γX(c, ·)` increases strictly on `[0, 1]`, for `c > s + 1`. -/
theorem gammaXS_strictMonoOn (hb : 2 ≤ b) (hs : 0 < s) (hc : (s : ℝ) + 1 < c) :
    StrictMonoOn (gammaXS s b c) (Icc 0 1) := fun _ hx _ hy hxy =>
  div_lt_div_of_pos_right (neg_lt_neg (g2S_strictAntiOn_right hs hc hx hy hxy)) (logS_pos hb)

/-- `γX(·, θ)` increases on `[1, ∞)`, for `θ ≥ 0`. -/
theorem gammaXS_monotoneOn (hb : 2 ≤ b) (hθ : 0 ≤ θ) :
    MonotoneOn (fun c => gammaXS s b c θ) (Ici 1) := fun _ hx _ hy hxy =>
  div_le_div_of_nonneg_right (neg_le_neg (g2S_antitoneOn_left hθ hx hy hxy)) (logS_pos hb).le

/-! ### The exponents `q` and `γ_Q` -/

/-- `q(0) = 0`. -/
@[simp] theorem qS_zero : qS s b 0 = 0 := by simp [qS, entropy]

/-- `q` is continuous. -/
theorem continuous_qS : Continuous (qS s b) :=
  (entropy_continuous.add (continuous_id.mul continuous_const)).div_const _

/-- `q` increases strictly on `[0, s/(s+1)]`: the derivative of `H(θ) + θ ln s` is
`ln(s (1 - θ)/θ)`, positive for `0 < θ < s/(s+1)`. -/
theorem qS_strictMonoOn (hb : 2 ≤ b) (hs : 0 < s) :
    StrictMonoOn (qS s b) (Icc 0 ((s : ℝ) / (s + 1))) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hnum : StrictMonoOn (fun θ : ℝ => entropy θ + θ * log s) (Icc 0 ((s : ℝ) / (s + 1))) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (entropy_continuous.add (continuous_id.mul continuous_const)).continuousOn fun θ hθ => ?_
    rw [interior_Icc] at hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hθ1' : θ < 1 := hθ1.trans window_lt_one
    have hderiv : HasDerivAt (fun θ : ℝ => entropy θ + θ * log s)
        (log ((1 - θ) / θ) + 1 * log s) θ :=
      (hasDerivAt_entropy θ hθ0 hθ1').add ((hasDerivAt_id θ).mul_const (log s))
    rw [hderiv.deriv, one_mul, ← log_mul (div_pos (by linarith) hθ0).ne' hs'.ne']
    refine log_pos ?_
    rw [div_mul_eq_mul_div, lt_div_iff₀ hθ0]
    rw [lt_div_iff₀ (by positivity)] at hθ1
    linarith
  exact fun x hx y hy hxy => div_lt_div_of_pos_right (hnum hx hy hxy) (logS_pos hb)

/-- `q(s/(s+1)) = log_b(s + 1)`: indeed `H(x) + x ln s = ln(s + 1)` at `x = s/(s+1)`, because
`ln x = ln s - ln(s + 1)` and `ln(1 - x) = -ln(s + 1)`. -/
theorem qS_at_right (hs : 0 < s) : qS s b ((s : ℝ) / (s + 1)) = log ((s : ℝ) + 1) / log b := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (0 : ℝ) < s + 1 := by positivity
  have hx : log ((s : ℝ) / (s + 1)) = log s - log (s + 1) := log_div hs'.ne' hs1.ne'
  have h1x : (1 : ℝ) - s / (s + 1) = 1 / (s + 1) := by
    field_simp
    ring
  have hy : log (1 / ((s : ℝ) + 1)) = -log (s + 1) := by rw [one_div, log_inv]
  rw [qS, entropy, h1x, hx, hy]
  congr 1
  field_simp
  ring

/-- `γ_Q(0) = 2/3`. -/
@[simp] theorem gammaQS_zero : gammaQS s b 0 = 2 / 3 := by simp [gammaQS]

/-- `γ_Q` is continuous. -/
theorem continuous_gammaQS : Continuous (gammaQS s b) :=
  (continuous_const.sub (continuous_const.mul continuous_qS)).div_const _

/-- `γ_Q` decreases strictly on `[0, s/(s+1)]`. -/
theorem gammaQS_strictAntiOn (hb : 2 ≤ b) (hs : 0 < s) :
    StrictAntiOn (gammaQS s b) (Icc 0 ((s : ℝ) / (s + 1))) := by
  intro x hx y hy hxy
  have h := qS_strictMonoOn hb hs hx hy hxy
  unfold gammaQS
  linarith

/-- `γ_Q(s/(s+1)) < 0` when `b < (s + 1)²`: then `log_b(s + 1) > 1/2`. -/
theorem gammaQS_neg_at_right (hb : 2 ≤ b) (hs : 0 < s) (hsb : b < (s + 1) ^ 2) :
    gammaQS s b ((s : ℝ) / (s + 1)) < 0 := by
  have hlb := logS_pos hb
  have hq : 1 / 2 < qS s b ((s : ℝ) / (s + 1)) := by
    rw [qS_at_right hs, lt_div_iff₀ hlb]
    have h : log (b : ℝ) < log (((s : ℝ) + 1) ^ 2) :=
      log_lt_log (by exact_mod_cast (by omega : 0 < b)) (by exact_mod_cast hsb)
    rw [log_pow] at h
    push_cast at h
    linarith
  unfold gammaQS
  linarith

/-! ### The crossing point -/

/-- For `c > s + 1` the functions `γX(c, ·)` and `γ_Q` cross in `(0, s/(s+1))`. -/
theorem exists_crossingS (hb : 2 ≤ b) (hs : 0 < s) (hsb : b < (s + 1) ^ 2)
    (hc : (s : ℝ) + 1 < c) :
    ∃ θ ∈ Ioo (0 : ℝ) (s / (s + 1)), gammaXS s b c θ = gammaQS s b θ := by
  have hcont : ContinuousOn (fun θ => gammaXS s b c θ - gammaQS s b θ) (Icc 0 (s / (s + 1))) :=
    ((continuous_gammaXS_right c).sub continuous_gammaQS).continuousOn
  have h0 : gammaXS s b c 0 - gammaQS s b 0 < 0 := by
    rw [gammaXS_zero, gammaQS_zero]
    norm_num
  have h1 : 0 < gammaXS s b c (s / (s + 1)) - gammaQS s b (s / (s + 1)) := by
    have h := gammaXS_pos hb hs hc (window_pos hs) window_lt_one.le
    linarith [gammaQS_neg_at_right hb hs hsb]
  obtain ⟨θ, hθ, h⟩ := intermediate_value_Ioo (window_pos hs).le hcont ⟨h0, h1⟩
  exact ⟨θ, hθ, sub_eq_zero.1 h⟩

/-- `γX(c, ·)` increases strictly on `[0, s/(s+1)]`, for `c > s + 1`. -/
theorem gammaXS_strictMonoOn' (hb : 2 ≤ b) (hs : 0 < s) (hc : (s : ℝ) + 1 < c) :
    StrictMonoOn (gammaXS s b c) (Icc 0 ((s : ℝ) / (s + 1))) :=
  (gammaXS_strictMonoOn hb hs hc).mono (Icc_subset_Icc_right window_lt_one.le)

/-- At every `θ₀ ∈ [0, s/(s+1)]`, the smaller of `γX(c, θ₀)` and `γ_Q(θ₀)` is at most the common
value at the crossing point. -/
theorem min_le_of_crossingS (hb : 2 ≤ b) (hs : 0 < s) (hc : (s : ℝ) + 1 < c)
    (hθ : θ ∈ Ioo (0 : ℝ) (s / (s + 1))) (h : gammaXS s b c θ = gammaQS s b θ)
    (hθ₀ : θ₀ ∈ Icc (0 : ℝ) (s / (s + 1))) :
    min (gammaXS s b c θ₀) (gammaQS s b θ₀) ≤ gammaXS s b c θ := by
  have hθ' := Ioo_subset_Icc_self hθ
  rcases le_total θ₀ θ with h' | h'
  · exact (min_le_left _ _).trans ((gammaXS_strictMonoOn' hb hs hc).monotoneOn hθ₀ hθ' h')
  · rw [h]
    exact (min_le_right _ _).trans ((gammaQS_strictAntiOn hb hs).antitoneOn hθ' hθ₀ h')

/-- At every `θ₀ ∈ [0, s/(s+1)]`, the larger of `γX(c, θ₀)` and `γ_Q(θ₀)` is at least the common
value at the crossing point. -/
theorem le_max_of_crossingS (hb : 2 ≤ b) (hs : 0 < s) (hc : (s : ℝ) + 1 < c)
    (hθ : θ ∈ Ioo (0 : ℝ) (s / (s + 1))) (h : gammaXS s b c θ = gammaQS s b θ)
    (hθ₀ : θ₀ ∈ Icc (0 : ℝ) (s / (s + 1))) :
    gammaXS s b c θ ≤ max (gammaXS s b c θ₀) (gammaQS s b θ₀) := by
  have hθ' := Ioo_subset_Icc_self hθ
  rcases le_total θ θ₀ with h' | h'
  · exact ((gammaXS_strictMonoOn' hb hs hc).monotoneOn hθ' hθ₀ h').trans (le_max_left _ _)
  · rw [h]
    exact ((gammaQS_strictAntiOn hb hs).antitoneOn hθ₀ hθ' h').trans (le_max_right _ _)

/-- `Γ(c)` is the common value of `γX(c, ·)` and `γ_Q` at their crossing point. -/
theorem GamS_eq_of_crossing (hb : 2 ≤ b) (hs : 0 < s) (hc : (s : ℝ) + 1 < c)
    (hθ : θ ∈ Ioo (0 : ℝ) (s / (s + 1))) (h : gammaXS s b c θ = gammaQS s b θ) :
    GamS s b c = gammaXS s b c θ := by
  unfold GamS
  refine IsGreatest.csSup_eq ⟨⟨θ, hθ, by simp [h]⟩, ?_⟩
  rintro _ ⟨θ₀, hθ₀, rfl⟩
  exact min_le_of_crossingS hb hs hc hθ h (Ioo_subset_Icc_self hθ₀)

/-- For `c > s + 1` there is `θ* ∈ (0, s/(s+1))` with `γX(c, θ*) = Γ(c) = γ_Q(θ*)`. -/
theorem exists_crossing_eq_GamS (hb : 2 ≤ b) (hs : 0 < s) (hsb : b < (s + 1) ^ 2)
    (hc : (s : ℝ) + 1 < c) :
    ∃ θ ∈ Ioo (0 : ℝ) (s / (s + 1)), gammaXS s b c θ = GamS s b c ∧ gammaQS s b θ = GamS s b c := by
  obtain ⟨θ, hθ, h⟩ := exists_crossingS hb hs hsb hc
  have hG := GamS_eq_of_crossing hb hs hc hθ h
  exact ⟨θ, hθ, hG.symm, by rw [← h, hG]⟩

/-- `Γ(c) > 0` for `c > s + 1`. -/
theorem GamS_pos (hb : 2 ≤ b) (hs : 0 < s) (hsb : b < (s + 1) ^ 2) (hc : (s : ℝ) + 1 < c) :
    0 < GamS s b c := by
  obtain ⟨θ, hθ, hX, -⟩ := exists_crossing_eq_GamS hb hs hsb hc
  rw [← hX]
  exact gammaXS_pos hb hs hc hθ.1 (hθ.2.trans window_lt_one).le

/-- `Γ(c) < 2/3` for `c > s + 1`. -/
theorem GamS_lt_two_thirds (hb : 2 ≤ b) (hs : 0 < s) (hsb : b < (s + 1) ^ 2)
    (hc : (s : ℝ) + 1 < c) : GamS s b c < 2 / 3 := by
  obtain ⟨θ, hθ, -, hQ⟩ := exists_crossing_eq_GamS hb hs hsb hc
  rw [← hQ, ← gammaQS_zero (s := s) (b := b)]
  exact gammaQS_strictAntiOn hb hs (left_mem_Icc.2 (window_pos hs).le) (Ioo_subset_Icc_self hθ)
    hθ.1

/-- **Lower bound for `Γ`**: `min(γX(c, θ₀), γ_Q(θ₀)) ≤ Γ(c)` for every `θ₀ ∈ (0, s/(s+1))`. -/
theorem GamS_ge_min (hb : 2 ≤ b) (hs : 0 < s) (hsb : b < (s + 1) ^ 2) (hc : (s : ℝ) + 1 < c)
    (hθ₀ : θ₀ ∈ Ioo (0 : ℝ) (s / (s + 1))) :
    min (gammaXS s b c θ₀) (gammaQS s b θ₀) ≤ GamS s b c := by
  obtain ⟨θ, hθ, h⟩ := exists_crossingS hb hs hsb hc
  rw [GamS_eq_of_crossing hb hs hc hθ h]
  exact min_le_of_crossingS hb hs hc hθ h (Ioo_subset_Icc_self hθ₀)

/-- **Upper bound for `Γ`**: `Γ(c) ≤ max(γX(c, θ₀), γ_Q(θ₀))` for every `θ₀ ∈ (0, s/(s+1))`. -/
theorem GamS_le_max (hb : 2 ≤ b) (hs : 0 < s) (hsb : b < (s + 1) ^ 2) (hc : (s : ℝ) + 1 < c)
    (hθ₀ : θ₀ ∈ Ioo (0 : ℝ) (s / (s + 1))) :
    GamS s b c ≤ max (gammaXS s b c θ₀) (gammaQS s b θ₀) := by
  obtain ⟨θ, hθ, h⟩ := exists_crossingS hb hs hsb hc
  rw [GamS_eq_of_crossing hb hs hc hθ h]
  exact le_max_of_crossingS hb hs hc hθ h (Ioo_subset_Icc_self hθ₀)

/-- `Γ` is nondecreasing on `(s + 1, ∞)`, because `γX` is nondecreasing in `c`. -/
theorem GamS_monotoneOn (hb : 2 ≤ b) (hs : 0 < s) (hsb : b < (s + 1) ^ 2) :
    MonotoneOn (GamS s b) (Ioi ((s : ℝ) + 1)) := by
  intro c₁ hc₁ c₂ hc₂ h
  have hc₁' : (s : ℝ) + 1 < c₁ := hc₁
  have hc₂' : (s : ℝ) + 1 < c₂ := hc₂
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  obtain ⟨θ, hθ, hX, hQ⟩ := exists_crossing_eq_GamS hb hs hsb hc₁'
  have hmono : gammaXS s b c₁ θ ≤ gammaXS s b c₂ θ :=
    gammaXS_monotoneOn hb hθ.1.le (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) h
  calc GamS s b c₁ = min (gammaXS s b c₁ θ) (gammaQS s b θ) := by rw [hX, hQ, min_self]
    _ ≤ min (gammaXS s b c₂ θ) (gammaQS s b θ) := min_le_min_right _ hmono
    _ ≤ GamS s b c₂ := GamS_ge_min hb hs hsb hc₂' hθ

/-! ### The thinness constant -/

/-- `basePrunedS s c = (1/2) c H(1/c) + (c - 1) (ln s)/2`, with `c H(1/c)` as `cEntropy c`. -/
theorem basePrunedS_eq (hc : 1 < c) :
    basePrunedS s c = 1 / 2 * cEntropy c + (c - 1) * log s / 2 := by
  rw [← mul_entropy_one_div hc, basePrunedS]
  ring

/-- `basePrunedS s c > 0` for `s ≥ 2` and `c > 1`. -/
theorem basePrunedS_pos (hs : 2 ≤ s) (hc : 1 < c) : 0 < basePrunedS s c := by
  have hc0 : 0 < c := by linarith
  have hH : 0 ≤ entropy (1 / c) :=
    entropy_nonneg (by positivity) ((div_le_one hc0).2 hc.le)
  have h3 : 0 < (c - 1) * log s / 2 :=
    div_pos (mul_pos (sub_pos.2 hc) (logS_pos hs)) two_pos
  have h2 : 0 ≤ c / 2 * entropy (1 / c) := mul_nonneg (by positivity) hH
  unfold basePrunedS
  linarith

/-- `basePrunedS s` is nondecreasing on `(1, ∞)` for `s ≥ 1`: its derivative is
`(1/2) (ln c - ln(c - 1)) + (ln s)/2 ≥ 0`. -/
theorem basePrunedS_monotoneOn (hs : 0 < s) : MonotoneOn (basePrunedS s) (Ioi 1) := by
  have hder : ∀ c : ℝ, 1 < c →
      HasDerivAt (fun c : ℝ => 1 / 2 * cEntropy c + (c - 1) * log s / 2)
        (1 / 2 * (log c - log (c - 1)) + 1 * log s / 2) c := fun c hc =>
    ((hasDerivAt_cEntropy hc).const_mul (1 / 2)).add
      ((((hasDerivAt_id c).sub_const 1).mul_const (log s)).div_const 2)
  have key : MonotoneOn (fun c : ℝ => 1 / 2 * cEntropy c + (c - 1) * log s / 2) (Ioi 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 1) ?_ ?_ ?_
    · have := continuous_cEntropy
      fun_prop
    · intro c hc
      rw [interior_Ioi] at hc
      exact (hder c hc).differentiableAt.differentiableWithinAt
    · intro c hc
      rw [interior_Ioi] at hc
      have hc' : 1 < c := hc
      rw [(hder c hc').deriv]
      have h2 : log (c - 1) ≤ log c := log_le_log (by linarith) (by linarith)
      have h3 := logS_nonneg hs
      linarith
  intro x hx y hy hxy
  rw [basePrunedS_eq hx, basePrunedS_eq hy]
  exact key hx hy hxy

end ImprovedExponents
