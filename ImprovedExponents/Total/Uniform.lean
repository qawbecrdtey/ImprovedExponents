module

public import ImprovedExponents.Pipeline.HostBound

@[expose] public section

/-!
# From the explicit bound to a bound for all sizes and all bounds on the weights

`exactTriangleUniform_of_explicitFrom` is upstream's `exactTriangleUniform_of_explicit` with the
threshold `16^18` replaced by the threshold `n₀` of `ExplicitFrom`: below `max n₀ 3` vertices per
part the instance is solved by brute force, from there on by the explicit bound with
`κ = max 1 (log u / log s)`.
-/

namespace ImprovedExponents

open ThreeSumApsp

-- The next six declarations are adapted from upstream
-- `ThreeSumApsp/TimeClaims/Sec3/Theorem19.lean`, where they are private; in
-- `dominated_explicitFrom` the threshold `16^18` is replaced by an arbitrary one.

/-- The time `uniformTime` without its constant: `s^{3-δ} (log s + 1)^e (1 + log u)²`. -/
noncomputable abbrev uniformShape (δ : ℝ) (e : ℕ) (p : SizeBound) : ℝ :=
  (p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e * (1 + logU p.u) ^ 2

/-- Each of the three factors of `uniformShape` is at least 1. -/
theorem one_le_uniformShape {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1) {p : SizeBound} (hs : 1 ≤ p.s) :
    1 ≤ uniformShape δ e p :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (Nat.one_le_cast.2 hs) (by linarith)) (one_le_log_add_one_pow p.s e))
    (one_le_pow₀ (one_le_one_add_logU p.u))

/-- "Smaller instances are solved by brute force": below a fixed size `n₀`, the time
`s³ (1 + log u)` is `O(s^{3-δ} (log s + 1)^e (1 + log u)²)`, because `s^δ ≤ n₀^δ`. -/
theorem dominated_bruteForce {δ : ℝ} (e n₀ : ℕ) (hδ0 : 0 ≤ δ) :
    Dominated (fun p : SizeBound => (1 ≤ p.s ∧ 1 ≤ p.u) ∧ p.s < n₀)
      (fun p => (p.s : ℝ) ^ 3 * (1 + logU p.u)) (uniformShape δ e) := by
  refine .of_le_const_mul (C := (n₀ : ℝ) ^ δ) (by positivity) fun p hp => ?_
  have hlog := one_le_log_add_one_pow p.s e
  have hwords := one_le_one_add_logU p.u
  have hs0 : (0 : ℝ) < p.s := Nat.cast_pos.2 hp.1.1
  have hsplit : (p.s : ℝ) ^ 3 = (p.s : ℝ) ^ δ * (p.s : ℝ) ^ (3 - δ) := by
    rw [← Real.rpow_add hs0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hsmall : (p.s : ℝ) ^ δ ≤ (n₀ : ℝ) ^ δ :=
    Real.rpow_le_rpow hs0.le (Nat.cast_le.2 hp.2.le) hδ0
  calc (p.s : ℝ) ^ 3 * (1 + logU p.u)
      = (p.s : ℝ) ^ δ * ((p.s : ℝ) ^ (3 - δ) * 1 * (1 + logU p.u) ^ 1) := by rw [hsplit]; ring
    _ ≤ (n₀ : ℝ) ^ δ * ((p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e * (1 + logU p.u) ^ 2) := by
        gcongr
        norm_num

/-- Weights up to `u` are weights up to `s^κ` for `κ = max 1 (log u / log s)`. -/
theorem le_rpow_max_log_div {s : ℕ} {u : ℝ} (hs : 3 ≤ s) (hu : 1 ≤ u) :
    u ≤ (s : ℝ) ^ max 1 (Real.log u / Real.log s) := by
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.2 (by omega)
  have hlogs : 1 ≤ Real.log s := Real.one_le_log_natCast_of_three_le hs
  calc u = (s : ℝ) ^ (Real.log u / Real.log s) := by
        rw [Real.rpow_def_of_pos hs0, mul_div_cancel₀ _ (by linarith),
          Real.exp_log (zero_lt_one.trans_le hu)]
    _ ≤ (s : ℝ) ^ max 1 (Real.log u / Real.log s) :=
        Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 (by omega)) (le_max_right _ _)

/-- The exponent `max 1 (log u / log s)` is at most `1 + log u`. -/
theorem max_log_div_le {s : ℕ} {u : ℝ} (hs : 3 ≤ s) (hu : 1 ≤ u) :
    max 1 (Real.log u / Real.log s) ≤ 1 + logU u := by
  refine max_le (one_le_one_add_logU u) ?_
  linarith [div_le_self (Real.log_nonneg hu) (Real.one_le_log_natCast_of_three_le hs),
    log_le_logU (zero_lt_one.trans_le hu)]

/-- From a size `n₁ ≥ max n₀ 3` on: the explicit bound, valid from `n₀` on, with
`κ = max 1 (log u / log s)`. -/
theorem dominated_explicitFrom {T : ℕ → ℝ → ℝ} {K δ : ℝ} {e n₀ n₁ : ℕ} (h0 : n₀ ≤ n₁)
    (h3 : 3 ≤ n₁)
    (hb : ∀ (n : ℕ) (κ u : ℝ), n₀ ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))) :
    Dominated (fun p : SizeBound => (1 ≤ p.s ∧ 1 ≤ p.u) ∧ ¬ p.s < n₁) (fun p => T p.s p.u)
      (uniformShape δ e) := by
  have h3' : ∀ p : SizeBound, ¬ p.s < n₁ → 3 ≤ p.s := fun p hp => h3.trans (not_lt.1 hp)
  refine (Dominated.of_exists_const (g := fun p => max 1 (Real.log p.u / Real.log p.s) *
    ((p.s : ℝ) ^ (3 - δ) * Real.log p.s ^ e)) ⟨K, fun p hp => ?_⟩ fun p _ => ?_).trans
    (.of_le fun p hp => ?_)
  · exact hb p.s _ p.u (h0.trans (not_lt.1 hp.2)) (le_max_left _ _)
      (le_rpow_max_log_div (h3' p hp.2) hp.1.2)
  · positivity
  · have hκ := max_log_div_le (h3' p hp.2) hp.1.2
    have hlog := Real.log_natCast_nonneg p.s
    have hwords := le_self_pow₀ (one_le_one_add_logU p.u) two_ne_zero
    calc max 1 (Real.log p.u / Real.log p.s) * ((p.s : ℝ) ^ (3 - δ) * Real.log p.s ^ e)
        ≤ (1 + logU p.u) ^ 2 * ((p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e) := by
          gcongr
          · exact hκ.trans hwords
          · linarith
      _ = uniformShape δ e p := by ring

/-- From the explicit bound from some size on (`ExplicitFrom`), brute force for the smaller
instances and the two closure properties: Exact Triangle in time
`K s^{3-δ} (log s + 1)^e (1 + log u)²` for all `s` and `u`. (Upstream's
`exactTriangleUniform_of_explicit` for an arbitrary threshold.) -/
theorem exactTriangleUniform_of_explicitFrom (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hex : ExplicitFrom M δ e) (hbf : Claim.BruteForce M)
    (hch : Closure.ChooseBySize M) (hmono : Closure.MonoExactTriangle M) :
    Claim.ExactTriangleUniform M δ e := by
  obtain ⟨n₀, K, T, hT, hb⟩ := hex
  obtain ⟨C, hbf⟩ := hbf
  obtain ⟨C₀, hch⟩ := hch (max n₀ 3)
  have hshape : ∀ p : SizeBound, 1 ≤ p.s ∧ 1 ≤ p.u → 1 ≤ uniformShape δ e p := fun p hp =>
    one_le_uniformShape e hδ1 hp.1
  have hsmall := (dominated_bruteForce e (max n₀ 3) hδ0).const_mul_of_nonneg C fun p _ =>
    mul_nonneg (by positivity) (zero_le_one.trans (one_le_one_add_logU p.u))
  obtain ⟨K', hK'0, hK'⟩ := (Dominated.ite hsmall
    (dominated_explicitFrom (le_max_left _ _) (le_max_right _ _) hb) fun p hp =>
    zero_le_one.trans (hshape p hp)).add (.const C₀ hshape)
  refine ⟨1 + K', le_add_of_nonneg_right hK'0,
    hmono _ _ (fun s u hs hu => ?_) (hch _ T hbf hT)⟩
  exact (hK' ⟨s, u⟩ ⟨hs, hu⟩).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
    (zero_le_one.trans (hshape ⟨s, u⟩ ⟨hs, hu⟩)))

end ImprovedExponents
