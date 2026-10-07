module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ImprovedExponents.Cost8X.Within

@[expose] public section

/-!
# The costs of the programs with rational parameters, against `cost8X`

Upstream bounds the time of the offline routine of Section 4.4 by a constant times `tp + w tq` for
all bounds `tp`, `tq` that dominate the two costs of Theorem 30
(`Light.Sec4.exists_tOffline32_le`); the hypothesis is the structure `Light.Sec4.CostsWithin`,
which names `ThreeSumApsp.cost8`. This file has the same statement with `cost8X` in its place:
`CostsWithinX` and `exists_tOffline32_leX`. The program is upstream's.

The proofs are adapted from upstream `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Costs.lean`
(Apache-2.0). The time of a query does not involve the expression (8) and is taken from upstream
(`CostsWithinX.toCostsWithin`).
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec4

/-- The cost `cost8X` of the preprocessing of Theorem 30 at the parameters `G`. -/
noncomputable abbrev preCostX (G : RatParams) (N D₀ : ℕ) : ℝ :=
  cost8X (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N

/-- **The two bounds dominate the two costs**, at the sizes `N` and `D`, with `cost8X` in the
place of the expression (8): sizes and bounds are at least 1, `D ≤ N`, and from the threshold on
the hypotheses of Theorem 30 hold and `cost8X` and `L ∑ α_d` are at most `C tp` and `C tq`. -/
structure CostsWithinX (G : RatParams) (C : ℝ) (N D₀ : ℕ) (tp tq : ℝ) : Prop where
  /-- The size is at least 1. -/
  one_le_N : 1 ≤ N
  /-- The inner dimension is at least 1. -/
  one_le_D : 1 ≤ D₀
  /-- The inner dimension is at most the size. -/
  D_le_N : D₀ ≤ N
  /-- The bound on the preprocessing is at least 1. -/
  one_le_pre : 1 ≤ tp
  /-- The bound on a query is at least 1. -/
  one_le_query : 1 ≤ tq
  /-- From the threshold on: the hypotheses of Theorem 30 and the two costs. -/
  above : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀) ∧
    cost8X (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N ≤ C * tp ∧
    costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) ≤ C * tq

variable {G : RatParams}

/-- For `m ≥ m₀` the hypotheses of Theorem 30 hold. -/
theorem CostsWithinX.hyp {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithinX G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.Hyp N D₀ :=
  (h.above hm).1

/-- For `m ≥ m₀` the cost `cost8X` is at most `C tp`. -/
theorem CostsWithinX.pre_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithinX G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : preCostX G N D₀ ≤ C * tp :=
  (h.above hm).2.1

/-- For `m ≥ m₀` the cost of a query is at most `C tq`. -/
theorem CostsWithinX.query_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithinX G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.queryCost D₀ ≤ C * tq :=
  (h.above hm).2.2

/-- The bound on a query, as upstream wants it: the expression (8) is dominated by itself. This
gives upstream's facts about queries, which do not involve (8). -/
theorem CostsWithinX.toCostsWithin {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ}
    (h : CostsWithinX G C N D₀ tp tq) :
    CostsWithin G (max C 1) N D₀ (max 1 (G.preCost N D₀)) tq := by
  refine ⟨h.one_le_N, h.one_le_D, h.D_le_N, le_max_left _ _, h.one_le_query, fun hm =>
    ⟨h.hyp hm, ?_, (h.query_le hm).trans ?_⟩⟩
  · exact (le_max_right 1 _).trans (le_mul_of_one_le_left (by positivity) (le_max_right C 1))
  · exact mul_le_mul_of_nonneg_right (le_max_left C 1) (zero_le_one.trans h.one_le_query)

/-- From the threshold on the preprocessing takes `O(cost8X)` steps. -/
theorem exists_tPre31_le_cost8X (G : RatParams) (c0 : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N D₀ : ℕ, 1 ≤ N →
    G.m₀ ≤ logFour D₀ → G.Hyp N D₀ → (tPre31 c0 G N D₀ : ℝ) ≤ K * preCostX G N D₀ := by
  obtain ⟨k, hk⟩ := exists_tPre31_le_setup G
  obtain ⟨Cp, hCp0, hCp⟩ := exists_tPreCore_leX c0
  refine ⟨k * 7 + Cp, by positivity, fun N D₀ hN hm h => ?_⟩
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL0 : (0 : ℝ) ≤ (G.L (logFour D₀) : ℝ) := by positivity
  have hcore : (tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ)
      ≤ Cp * preCostX G N D₀ := hCp (parOf G N D₀) (switchOf31 G D₀) h
  have hNF : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ preCostX G N D₀ := N_mul_pow_le_cost8X h
  have hNL : (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) ≤ 3 * preCostX G N D₀ := N_mul_le_cost8X h
  have hsetup : (tPre31 c0 G N D₀ : ℝ)
      ≤ k * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
        + (tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ) := by exact_mod_cast hk c0 N D₀ hm
  -- L + 1 ≤ N (L + 1) and N ≤ N (L + 1), so that the sum is at most 7 times `cost8X`
  have hL : (G.L (logFour D₀) : ℝ) + 1 ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_left (by positivity) hN'
  have hNle : (N : ℝ) ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have hsum : (k : ℝ) * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
      ≤ k * (7 * preCostX G N D₀) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **The time of the preprocessing** is at most a constant times every bound `tp ≥ 1` that, from
the threshold on, dominates `cost8X`. -/
theorem exists_tPre31_leX (G : RatParams) {C : ℝ} (hC : 0 ≤ C) (c0 : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithinX G C N D₀ tp tq → (tPre31 c0 G N D₀ : ℝ) ≤ A * tp := by
  obtain ⟨K, hK0, hK⟩ := exists_tPre31_le_cost8X G c0
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((20 * G.m₀ + 50 : ℕ) : ℝ)) (by positivity) hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tp _ h.one_le_pre h.pre_le (fun hm => ?_) fun hm => ?_⟩
  · have hsmall : tPre31 c0 G N D₀ ≤ 20 * G.m₀ + 50 := by
      unfold tPre31 tLog4
      rw [if_pos hm]
      omega
    exact_mod_cast hsmall
  · have := hK N D₀ h.one_le_N hm (h.hyp hm)
    have : (0 : ℝ) ≤ ((20 * G.m₀ + 50 : ℕ) : ℝ) := by positivity
    linarith

/-- **The time of the offline routine**, with `k` further steps, is at most a constant times
`tp + w tq`, for all bounds `tp, tq ≥ 1` that dominate `cost8X` and the cost of a query. -/
theorem exists_tOffline32_leX (G : RatParams) {C : ℝ} (hC : 0 ≤ C) (c0 k : ℕ) : ∃ A : ℝ,
    ∀ {N D₀ : ℕ} {tp tq : ℝ} (w : ℕ), CostsWithinX G C N D₀ tp tq →
      (tOffline32 c0 G N D₀ w : ℝ) + k ≤ A * (tp + w * tq) := by
  obtain ⟨Ap, hAp0, hAp⟩ := exists_tPre31_leX G hC c0
  obtain ⟨Aq, hAq0, hAq⟩ := exists_tQuery31_le G (hC.trans (le_max_left C 1))
  refine ⟨(Ap + 20 + k) + (Aq + 30), fun {N D₀ tp tq} w h => ?_⟩
  have hpre := hAp h
  have hquery := hAq h.toCostsWithin
  have htp := h.one_le_pre
  have htq := h.one_le_query
  have hw : (0 : ℝ) ≤ (w : ℝ) := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hwtq : 0 ≤ (w : ℝ) * tq := mul_nonneg hw (by linarith)
  have htime : (tOffline32 c0 G N D₀ w : ℝ)
      = (tPre31 c0 G N D₀ : ℝ) + (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) + 20 := by
    simp only [tOffline32]
    push_cast
    ring
  -- the preprocessing and the k + 20 further steps against tp, the w queries against w tq
  have hfirst : (tPre31 c0 G N D₀ : ℝ) + 20 + k ≤ (Ap + 20 + k) * tp := by
    linarith [le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 20 + (k : ℝ)) htp]
  have hsecond : (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) ≤ (Aq + 30) * ((w : ℝ) * tq) := by
    calc (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) ≤ (w : ℝ) * ((Aq + 30) * tq) :=
          mul_le_mul_of_nonneg_left (by linarith) hw
      _ = (Aq + 30) * ((w : ℝ) * tq) := by ring
  have hcross₁ : 0 ≤ (Ap + 20 + k) * ((w : ℝ) * tq) := mul_nonneg (by positivity) hwtq
  have hcross₂ : 0 ≤ (Aq + 30) * tp := mul_nonneg (by positivity) (by linarith)
  rw [htime]
  linarith

end ImprovedExponents
