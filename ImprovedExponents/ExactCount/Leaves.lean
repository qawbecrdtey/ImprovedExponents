module

public import ThreeSumApsp.Sec2.Theorem5
public import ImprovedExponents.ExactCount.Tail
import all ThreeSumApsp.Sec4.ChoosingParameters

@[expose] public section

/-!
# The leaves of the pruned recursion over all tiles, with the best split

Lemma 11 of the paper bounds the leaves that the pruned recursion visits on a set `U` of output
strings by `∑_{d ≤ m} min(|U| α_d, β_d)` (`ThreeSumApsp.Lemma11.first_inequality`, for all `L` and
`m`). For `L = 19m` the paper splits the sum at `d = m/9` and sums over the tiles
(`ThreeSumApsp.Theorem5.total_leaves`). Here the sum over the tiles is bounded for every `L ≥ 10m`
and every density of the wanted positions, with the split at the best order.

With `|W| ≤ N²/D^κ`, `D = 4^m`, and `L ≥ cm`, the two bounds at the order `d = δm` are, up to the
factor `16 (L + 1) N²`,

* `e^{m f₁(κ, δ)}` with `f₁(κ, δ) = -κ ln 4 + H(δ) + δ ln 9 = (q(δ) - κ) ln 4` (`f1`), from
  `∑_T |W_T| ≤ |W|` and `binom(m, d) ≤ e^{m H(d/m)}`;
* `e^{m g₂(c, δ)}` (`g2`), from `β_d ≤ (L + 1) M e^{m g₂(L/m, d/m)}` and `#tiles · M ≤ 4 N'²` for
  the padded size `N' ≤ 2N`.

So the number of leaves is at most `16 (m + 1)(L + 1) N² e^{m Γ(c, κ)}` with
`Γ(c, κ) = sup_{0 ≤ δ ≤ 1} min(f₁(κ, δ), g₂(c, δ))` (`GammaMM`, `sum_card_Leaves_le_exp`; in the
padded size `N'` it is `4 (m + 1)(L + 1) N'² e^{m Γ(c, κ)}`, `sum_card_Leaves_le_exp_padN`).

As `f₁(κ, ·)` increases on `[0, 9/10]` and `g₂(c, ·)` decreases on `[0, 1]`, the supremum is taken
where they cross: `min(f₁, g₂)(δ₀) ≤ Γ(c, κ) ≤ max(f₁, g₂)(δ₀)` for every `δ₀ ∈ [0, 9/10]`
(`min_le_GammaMM`, `GammaMM_le_max`, `GammaMM_eq_of_eq`). For `c > 10` and `0 < κ < log_4 10` they
do cross, and `Γ(c, κ) < 0` (`exists_crossing_f1_g2`).
-/

namespace ImprovedExponents

open ThreeSumApsp Real Finset

open private exp_entropy_eq from ThreeSumApsp.Sec4.ChoosingParameters

/-! ### The two exponents and their supremum -/

/-- The exponent `f₁(κ, δ) = -κ ln 4 + H(δ) + δ ln 9` of the bound `|W| α_d` at the order `d = δm`,
relative to `N²`, when `|W| ≤ N²/D^κ`. -/
noncomputable def f1 (κ δ : ℝ) : ℝ := -κ * log 4 + entropy δ + δ * log 9

/-- The exponent of the number of leaves: `Γ(c, κ) = sup_{0 ≤ δ ≤ 1} min(f₁(κ, δ), g₂(c, δ))`. -/
noncomputable def GammaMM (c κ : ℝ) : ℝ :=
  sSup ((fun δ => min (f1 κ δ) (g2 c δ)) '' Set.Icc 0 1)

/-- `f₁(κ, δ) = (q(δ) - κ) ln 4` with the `q` of the paper's Section 4.4. -/
theorem f1_eq (κ δ : ℝ) : f1 κ δ = (qOf δ - κ) * log 4 := by
  have h4 := log_four_pos.ne'
  unfold f1 qOf
  field_simp
  ring

/-- `f₁(κ, ·)` is continuous. -/
theorem continuous_f1 (κ : ℝ) : Continuous (f1 κ) :=
  (continuous_const.add entropy_continuous).add (continuous_id.mul continuous_const)

/-- `f₁(κ, ·)` increases strictly on `[0, 9/10]` (upstream's `qOf_strictMonoOn`). -/
theorem f1_strictMonoOn (κ : ℝ) : StrictMonoOn (f1 κ) (Set.Icc 0 (9 / 10)) := by
  have hq : StrictMonoOn qOf (Set.Icc 0 (9 / 10)) := by
    have h := qOf_strictMonoOn
    rwa [show (0.9 : ℝ) = 9 / 10 by norm_num] at h
  intro x hx y hy hxy
  rw [f1_eq, f1_eq]
  exact mul_lt_mul_of_pos_right (sub_lt_sub_right (hq hx hy hxy) κ) log_four_pos

/-- The values `min(f₁(κ, δ), g₂(c, δ))` for `0 ≤ δ ≤ 1` are bounded above: a continuous function
on a compact interval. -/
theorem bddAbove_min_f1_g2 (c κ : ℝ) :
    BddAbove ((fun δ => min (f1 κ δ) (g2 c δ)) '' Set.Icc 0 1) :=
  isCompact_Icc.bddAbove_image ((continuous_f1 κ).min (continuous_g2_right c)).continuousOn

/-- `min(f₁(κ, δ), g₂(c, δ)) ≤ Γ(c, κ)` for `0 ≤ δ ≤ 1`. -/
theorem min_le_GammaMM (c κ : ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    min (f1 κ δ) (g2 c δ) ≤ GammaMM c κ :=
  le_csSup (bddAbove_min_f1_g2 c κ) (Set.mem_image_of_mem _ ⟨hδ0, hδ1⟩)

/-- `Γ(c, κ) ≤ max(f₁(κ, δ₀), g₂(c, δ₀))` for every `δ₀ ∈ [0, 9/10]`, when `c ≥ 10`: below `δ₀` the
increasing `f₁` is at most its value at `δ₀`, above `δ₀` the decreasing `g₂` is. -/
theorem GammaMM_le_max {c : ℝ} (hc : 10 ≤ c) (κ : ℝ) {δ₀ : ℝ} (h0 : 0 ≤ δ₀) (h1 : δ₀ ≤ 9 / 10) :
    GammaMM c κ ≤ max (f1 κ δ₀) (g2 c δ₀) := by
  refine csSup_le ((Set.nonempty_Icc.2 zero_le_one).image _) ?_
  rintro _ ⟨δ, ⟨hδ0, hδ1⟩, rfl⟩
  rcases le_total δ δ₀ with h | h
  · exact (min_le_left _ _).trans (((f1_strictMonoOn κ).monotoneOn ⟨hδ0, h.trans h1⟩ ⟨h0, h1⟩
      h).trans (le_max_left _ _))
  · exact (min_le_right _ _).trans ((g2_antitoneOn_right hc ⟨h0, by linarith⟩ ⟨hδ0, hδ1⟩
      h).trans (le_max_right _ _))

/-- **The exponent at the crossing**: if `f₁(κ, δ₀) = g₂(c, δ₀)` at some `δ₀ ∈ [0, 9/10]` and
`c ≥ 10`, then `Γ(c, κ)` is this common value. -/
theorem GammaMM_eq_of_eq {c : ℝ} (hc : 10 ≤ c) (κ : ℝ) {δ₀ : ℝ} (h0 : 0 ≤ δ₀) (h1 : δ₀ ≤ 9 / 10)
    (h : f1 κ δ₀ = g2 c δ₀) : GammaMM c κ = g2 c δ₀ := by
  refine le_antisymm ?_ ?_
  · simpa [h] using GammaMM_le_max hc κ h0 h1
  · simpa [h] using min_le_GammaMM c κ h0 (h1.trans (by norm_num))

/-- **The crossing exists and the exponent is negative**: for `c > 10` and `0 < κ < log_4 10` the
two exponents cross at some `0 < δ₀ < 9/10`, where `Γ(c, κ) = g₂(c, δ₀) = f₁(κ, δ₀) < 0`. Indeed
`f₁(κ, 0) = -κ ln 4 < 0 = g₂(c, 0)` and `f₁(κ, 9/10) = (log_4 10 - κ) ln 4 > 0 > g₂(c, 9/10)`. -/
theorem exists_crossing_f1_g2 {c κ : ℝ} (hc : 10 < c) (hκ0 : 0 < κ) (hκ : κ < Real.logb 4 10) :
    ∃ δ₀ ∈ Set.Ioo (0 : ℝ) (9 / 10),
      f1 κ δ₀ = g2 c δ₀ ∧ GammaMM c κ = g2 c δ₀ ∧ GammaMM c κ < 0 := by
  have h4 := log_four_pos
  have hcont : ContinuousOn (fun δ => f1 κ δ - g2 c δ) (Set.Icc 0 (9 / 10)) :=
    ((continuous_f1 κ).sub (continuous_g2_right c)).continuousOn
  have h0 : f1 κ 0 - g2 c 0 < 0 := by
    have h : f1 κ 0 = -κ * log 4 := by simp [f1, entropy_zero]
    rw [h, g2_zero]
    nlinarith
  have h9 : 0 < f1 κ (9 / 10) - g2 c (9 / 10) := by
    have hg : g2 c (9 / 10) < 0 := g2_neg hc (by norm_num) (by norm_num)
    have hf : 0 < f1 κ (9 / 10) := by
      rw [f1_eq, show (9 / 10 : ℝ) = 0.9 by norm_num, qOf_nine_tenths]
      exact mul_pos (sub_pos.2 hκ) h4
    linarith
  obtain ⟨δ₀, hδ₀, hz⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 9 / 10) hcont ⟨h0, h9⟩
  have heq : f1 κ δ₀ = g2 c δ₀ := sub_eq_zero.1 hz
  have hΓ := GammaMM_eq_of_eq hc.le κ hδ₀.1.le hδ₀.2.le heq
  exact ⟨δ₀, hδ₀, heq, hΓ, hΓ ▸ g2_neg hc hδ₀.1 (hδ₀.2.le.trans (by norm_num))⟩

/-! ### The two bounds at one order -/

/-- `binom(m, d) ≤ e^{m H(d/m)}`. -/
theorem choose_le_exp_entropy {m d : ℕ} (hm : 1 ≤ m) (hd : d ≤ m) :
    (m.choose d : ℝ) ≤ exp ((m : ℝ) * entropy ((d : ℝ) / m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set T : ℝ := ((d : ℝ) / m) ^ d * (1 - (d : ℝ) / m) ^ (m - d) with hTdef
  have hexp : exp ((m : ℝ) * entropy ((d : ℝ) / m)) = T⁻¹ := exp_entropy_eq d m hd hm
  have hT : 0 < T := inv_pos.1 (hexp ▸ exp_pos _)
  have hmm : (m : ℝ) ^ m = (m : ℝ) ^ d * (m : ℝ) ^ (m - d) := by
    rw [← pow_add, Nat.add_sub_cancel' hd]
  have h1 : 1 - (d : ℝ) / m = ((m - d : ℕ) : ℝ) / m := by
    rw [Nat.cast_sub hd]
    field_simp
  have hTn : T * (m : ℝ) ^ m = (d : ℝ) ^ d * ((m - d : ℕ) : ℝ) ^ (m - d) := by
    rw [hTdef, h1, hmm, div_pow, div_pow]
    field_simp
  have hnat : m.choose d * d ^ d * (m - d) ^ (m - d) ≤ m ^ m := by
    have h := Nat.choose_mul_pow_mul_pow_le d (m - d) m d
    rwa [Nat.add_sub_cancel' hd] at h
  have hcast : (m.choose d : ℝ) * (d : ℝ) ^ d * ((m - d : ℕ) : ℝ) ^ (m - d) ≤ (m : ℝ) ^ m := by
    exact_mod_cast hnat
  rw [hexp, ← one_div, le_div_iff₀ hT]
  refine le_of_mul_le_mul_right ?_ (pow_pos hm0 m)
  calc (m.choose d : ℝ) * T * (m : ℝ) ^ m
      = (m.choose d : ℝ) * (d : ℝ) ^ d * ((m - d : ℕ) : ℝ) ^ (m - d) := by
        rw [mul_assoc, hTn, mul_assoc]
    _ ≤ (m : ℝ) ^ m := hcast
    _ = 1 * (m : ℝ) ^ m := (one_mul _).symm

/-- `α_d/D^κ ≤ e^{m f₁(κ, d/m)}`. -/
theorem alpha_div_le_exp {m d : ℕ} (hm : 1 ≤ m) (hd : d ≤ m) (κ : ℝ) :
    (alpha m d : ℝ) / (D m : ℝ) ^ κ ≤ exp ((m : ℝ) * f1 κ ((d : ℝ) / m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h9 : exp ((d : ℝ) * log 9) = (9 : ℝ) ^ d := by
    rw [exp_nat_mul, exp_log (by norm_num)]
  have harg : (m : ℝ) * f1 κ ((d : ℝ) / m)
      = (m : ℝ) * entropy ((d : ℝ) / m) + (d : ℝ) * log 9 - κ * ((m : ℝ) * log 4) := by
    have h : (m : ℝ) * ((d : ℝ) / m * log 9) = d * log 9 := by field_simp
    unfold f1
    linear_combination h
  have hsplit : exp ((m : ℝ) * f1 κ ((d : ℝ) / m))
      = exp ((m : ℝ) * entropy ((d : ℝ) / m)) * (9 : ℝ) ^ d / (D m : ℝ) ^ κ := by
    rw [cast_D_rpow, ← h9, ← exp_add, ← exp_sub, harg]
  rw [hsplit, alpha]
  push_cast
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (choose_le_exp_entropy hm hd) (by positivity))
    (rpow_nonneg (Nat.cast_nonneg _) _)

/-- The two bounds of Lemma 11 at the order `d`, summed over the tiles, are at most
`4 (L + 1) N'² e^{m Γ(c, κ)}`, where `N'` is the padded size. -/
theorem min_card_mul_le_exp {L m N d : ℕ} {c κ : ℝ} (W : Finset (Fin N × Fin N)) (hm : 1 ≤ m)
    (hL : 10 * m ≤ L) (hc1 : 1 ≤ c) (hcL : c * m ≤ L)
    (hW : (W.card : ℝ) ≤ (N : ℝ) ^ 2 / (D m : ℝ) ^ κ) (hd : d ≤ m) :
    min ((W.card : ℝ) * (alpha m d : ℝ)) (((tiles L m N).card : ℝ) * (beta L m d : ℝ))
      ≤ 4 * ((L : ℝ) + 1) * (padN L m N : ℝ) ^ 2 * exp ((m : ℝ) * GammaMM c κ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hδ0 : (0 : ℝ) ≤ (d : ℝ) / m := by positivity
  have hδ1 : (d : ℝ) / m ≤ 1 := (div_le_one hm0).2 (by exact_mod_cast hd)
  have hLm : c ≤ (L : ℝ) / m := (le_div_iff₀ hm0).2 hcL
  have hΓ := min_le_GammaMM c κ hδ0 hδ1
  -- the bound `|W| α_d`
  have ha : (W.card : ℝ) * (alpha m d : ℝ)
      ≤ (N : ℝ) ^ 2 * exp ((m : ℝ) * f1 κ ((d : ℝ) / m)) :=
    calc (W.card : ℝ) * (alpha m d : ℝ)
        ≤ (N : ℝ) ^ 2 / (D m : ℝ) ^ κ * (alpha m d : ℝ) :=
          mul_le_mul_of_nonneg_right hW (Nat.cast_nonneg _)
      _ = (N : ℝ) ^ 2 * ((alpha m d : ℝ) / (D m : ℝ) ^ κ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (alpha_div_le_exp hm hd κ) (sq_nonneg _)
  -- the bound `#tiles · β_d`
  have hg : g2 ((L : ℝ) / m) ((d : ℝ) / m) ≤ g2 c ((d : ℝ) / m) :=
    g2_antitoneOn_left hδ0 (Set.mem_Ici.2 hc1) (Set.mem_Ici.2 (hc1.trans hLm)) hLm
  have htiles : ((tiles L m N).card : ℝ) * (M L m : ℝ) ≤ 4 * (padN L m N : ℝ) ^ 2 := by
    exact_mod_cast card_tiles_mul_M_le L m N
  have hb : ((tiles L m N).card : ℝ) * (beta L m d : ℝ)
      ≤ 4 * ((L : ℝ) + 1) * (padN L m N : ℝ) ^ 2 * exp ((m : ℝ) * g2 c ((d : ℝ) / m)) :=
    calc ((tiles L m N).card : ℝ) * (beta L m d : ℝ)
        ≤ ((tiles L m N).card : ℝ) * (((L : ℝ) + 1) * (M L m : ℝ)
            * exp ((m : ℝ) * g2 (L / m) (d / m))) :=
          mul_le_mul_of_nonneg_left (beta_le_exp hm hL le_rfl hd) (Nat.cast_nonneg _)
      _ = ((tiles L m N).card : ℝ) * (M L m : ℝ) * (((L : ℝ) + 1)
            * exp ((m : ℝ) * g2 (L / m) (d / m))) := by ring
      _ ≤ 4 * (padN L m N : ℝ) ^ 2 * (((L : ℝ) + 1) * exp ((m : ℝ) * g2 c (d / m))) :=
          mul_le_mul htiles (mul_le_mul_of_nonneg_left
            (exp_le_exp.2 (mul_le_mul_of_nonneg_left hg hm0.le)) (by positivity))
            (by positivity) (by positivity)
      _ = _ := by ring
  have hpad : (N : ℝ) ≤ (padN L m N : ℝ) := by exact_mod_cast le_padN (by omega : m ≤ L) N
  have hX : (N : ℝ) ^ 2 ≤ 4 * ((L : ℝ) + 1) * (padN L m N : ℝ) ^ 2 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg N) hpad 2).trans
      (le_mul_of_one_le_left (sq_nonneg _) (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]))
  rcases le_total (f1 κ ((d : ℝ) / m)) (g2 c ((d : ℝ) / m)) with h | h
  · rw [min_eq_left h] at hΓ
    calc min ((W.card : ℝ) * (alpha m d : ℝ)) (((tiles L m N).card : ℝ) * (beta L m d : ℝ))
        ≤ (W.card : ℝ) * (alpha m d : ℝ) := min_le_left _ _
      _ ≤ (N : ℝ) ^ 2 * exp ((m : ℝ) * f1 κ ((d : ℝ) / m)) := ha
      _ ≤ 4 * ((L : ℝ) + 1) * (padN L m N : ℝ) ^ 2 * exp ((m : ℝ) * GammaMM c κ) :=
          mul_le_mul hX (exp_le_exp.2 (mul_le_mul_of_nonneg_left hΓ hm0.le)) (exp_pos _).le
            (by positivity)
  · rw [min_eq_right h] at hΓ
    calc min ((W.card : ℝ) * (alpha m d : ℝ)) (((tiles L m N).card : ℝ) * (beta L m d : ℝ))
        ≤ ((tiles L m N).card : ℝ) * (beta L m d : ℝ) := min_le_right _ _
      _ ≤ 4 * ((L : ℝ) + 1) * (padN L m N : ℝ) ^ 2 * exp ((m : ℝ) * g2 c ((d : ℝ) / m)) := hb
      _ ≤ 4 * ((L : ℝ) + 1) * (padN L m N : ℝ) ^ 2 * exp ((m : ℝ) * GammaMM c κ) :=
          mul_le_mul_of_nonneg_left (exp_le_exp.2 (mul_le_mul_of_nonneg_left hΓ hm0.le))
            (by positivity)

/-! ### The sum over the tiles -/

/-- Lemma 11 summed over the tiles, for all `L` and `m`: at every order `d` the tiles together have
at most `min(|W| α_d, #tiles · β_d)` leaves, because `∑_T min(a_T, b) ≤ min(∑_T a_T, #tiles · b)`
and `∑_T |W_T| ≤ |W|`. -/
theorem sum_card_Leaves_le_sum_min {L m N : ℕ} (lay : Layout L m) (W : Finset (Fin N × Fin N)) :
    ∑ T ∈ tiles L m N, (Leaves (wantedStrings lay W T.1 T.2)).card
      ≤ ∑ d ∈ range (m + 1), min (W.card * alpha m d) ((tiles L m N).card * beta L m d) := by
  calc ∑ T ∈ tiles L m N, (Leaves (wantedStrings lay W T.1 T.2)).card
      ≤ ∑ T ∈ tiles L m N, ∑ d ∈ range (m + 1),
          min ((wantedStrings lay W T.1 T.2).card * alpha m d) (beta L m d) :=
        sum_le_sum fun T _ => Lemma11.first_inequality _
          (card_innerSetO_of_mem_wantedStrings lay W T.1 T.2)
    _ = ∑ d ∈ range (m + 1), ∑ T ∈ tiles L m N,
          min ((wantedStrings lay W T.1 T.2).card * alpha m d) (beta L m d) := sum_comm
    _ ≤ _ := sum_le_sum fun d _ => le_min ?_ ?_
  · calc ∑ T ∈ tiles L m N, min ((wantedStrings lay W T.1 T.2).card * alpha m d) (beta L m d)
        ≤ ∑ T ∈ tiles L m N, (wantedStrings lay W T.1 T.2).card * alpha m d :=
          sum_le_sum fun T _ => min_le_left _ _
      _ = (∑ T ∈ tiles L m N, (wantedStrings lay W T.1 T.2).card) * alpha m d :=
          (sum_mul _ _ _).symm
      _ ≤ W.card * alpha m d := Nat.mul_le_mul_right _ (sum_card_wantedStrings_le lay W)
  · calc ∑ T ∈ tiles L m N, min ((wantedStrings lay W T.1 T.2).card * alpha m d) (beta L m d)
        ≤ ∑ _T ∈ tiles L m N, beta L m d := sum_le_sum fun T _ => min_le_right _ _
      _ = (tiles L m N).card * beta L m d := by rw [sum_const, smul_eq_mul]

/-- **The leaves of all tiles, with the best split**, in the padded size. Let `L ≥ 10m` and
`L ≥ cm` with `c ≥ 1`. If there are at most `N²/D^κ` wanted positions, `D = 4^m`, then the pruned
recursions of all tiles visit at most `4 (m + 1)(L + 1) N'² e^{m Γ(c, κ)}` leaves, where `N'` is
the padded size (`ThreeSumApsp.padN`), as in upstream's `ThreeSumApsp.card_tiles_mul_M_le`. -/
theorem sum_card_Leaves_le_exp_padN {L m N : ℕ} {c κ : ℝ} (lay : Layout L m)
    (W : Finset (Fin N × Fin N)) (hm : 1 ≤ m) (hL : 10 * m ≤ L) (hc1 : 1 ≤ c) (hcL : c * m ≤ L)
    (hW : (W.card : ℝ) ≤ (N : ℝ) ^ 2 / (D m : ℝ) ^ κ) :
    ((∑ T ∈ tiles L m N, (Leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ)
      ≤ 4 * ((m : ℝ) + 1) * ((L : ℝ) + 1) * (padN L m N : ℝ) ^ 2
        * exp ((m : ℝ) * GammaMM c κ) := by
  have hcast : ((∑ T ∈ tiles L m N, (Leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ)
      ≤ ∑ d ∈ range (m + 1),
          min ((W.card : ℝ) * (alpha m d : ℝ)) (((tiles L m N).card : ℝ) * (beta L m d : ℝ)) := by
    exact_mod_cast sum_card_Leaves_le_sum_min lay W
  calc ((∑ T ∈ tiles L m N, (Leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ)
      ≤ ∑ d ∈ range (m + 1),
          min ((W.card : ℝ) * (alpha m d : ℝ)) (((tiles L m N).card : ℝ) * (beta L m d : ℝ)) :=
        hcast
    _ ≤ ∑ _d ∈ range (m + 1),
          4 * ((L : ℝ) + 1) * (padN L m N : ℝ) ^ 2 * exp ((m : ℝ) * GammaMM c κ) :=
        sum_le_sum fun d hd =>
          min_card_mul_le_exp W hm hL hc1 hcL hW (Nat.lt_succ_iff.1 (mem_range.1 hd))
    _ = 4 * ((m : ℝ) + 1) * ((L : ℝ) + 1) * (padN L m N : ℝ) ^ 2
          * exp ((m : ℝ) * GammaMM c κ) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **The leaves of all tiles, with the best split.** Let `L ≥ 10m`, `L ≥ cm` with `c ≥ 1`, and let
the matrix be large enough for the tiling (`K₀ N₀ ≤ N`, so that the padding at most doubles `N`).
If there are at most `N²/D^κ` wanted positions, `D = 4^m`, then the pruned recursions of all tiles
visit at most `16 (m + 1)(L + 1) N² e^{m Γ(c, κ)}` leaves. Here `N` is the size of the input, not
the padded size; this is the reason for the constant `16 = 4 · 2²`, as in upstream's
`ThreeSumApsp.Theorem5.total_leaves`. -/
theorem sum_card_Leaves_le_exp {L m N : ℕ} {c κ : ℝ} (lay : Layout L m)
    (W : Finset (Fin N × Fin N)) (hm : 1 ≤ m) (hL : 10 * m ≤ L) (hc1 : 1 ≤ c) (hcL : c * m ≤ L)
    (hN : K0 L m * N0 L m ≤ N) (hW : (W.card : ℝ) ≤ (N : ℝ) ^ 2 / (D m : ℝ) ^ κ) :
    ((∑ T ∈ tiles L m N, (Leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ)
      ≤ 16 * ((m : ℝ) + 1) * ((L : ℝ) + 1) * (N : ℝ) ^ 2 * exp ((m : ℝ) * GammaMM c κ) := by
  have hpad : (padN L m N : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast padN_le_two_mul L m N hN
  have hsq : (padN L m N : ℝ) ^ 2 ≤ (2 * (N : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hpad 2
  calc ((∑ T ∈ tiles L m N, (Leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ)
      ≤ 4 * ((m : ℝ) + 1) * ((L : ℝ) + 1) * (padN L m N : ℝ) ^ 2
          * exp ((m : ℝ) * GammaMM c κ) := sum_card_Leaves_le_exp_padN lay W hm hL hc1 hcL hW
    _ ≤ 4 * ((m : ℝ) + 1) * ((L : ℝ) + 1) * (2 * (N : ℝ)) ^ 2
          * exp ((m : ℝ) * GammaMM c κ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity))
          (exp_pos _).le
    _ = 16 * ((m : ℝ) + 1) * ((L : ℝ) + 1) * (N : ℝ) ^ 2 * exp ((m : ℝ) * GammaMM c κ) := by
        ring

end ImprovedExponents
