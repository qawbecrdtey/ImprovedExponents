module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ImprovedExponents.Cost8P.Within
public import ImprovedExponents.PrunedProgram.Wrapper.Times

@[expose] public section

/-!
# The costs of the pruned programs with rational parameters, against `cost8P`

`ImprovedExponents.Cost8X.Costs` bounds the time of upstream's offline routine by a constant times
`tp + w tq` for all bounds `tp`, `tq` that dominate `cost8X` and the cost of a query
(`exists_tOffline32_leX`, hypothesis `CostsWithinX`). This file has the same statement for the
pruned offline routine, whose time functions `tPre31P`, `tOffline32P` have the time `tPreCoreP` of
the pruned preprocessing, against `cost8P`: `CostsWithinP` and `exists_tOffline32P_le`.

The proofs are adapted from upstream `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Costs.lean`
(Apache-2.0) and from `ImprovedExponents/Cost8X/Costs.lean`. The time of a query does not involve
the cost of the preprocessing and is taken from upstream (`CostsWithinP.toCostsWithin`); the
set-up before the preprocessing is upstream's (`exists_tPre31P_le_setup`).
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec4

/-- The cost `cost8P` of the pruned preprocessing of Theorem 30 at the parameters `G`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (preCostX)
noncomputable abbrev preCostP (G : RatParams) (N D₀ : ℕ) : ℝ :=
  cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N

/-- **The two bounds dominate the two costs**, at the sizes `N` and `D`, with `cost8P` in the
place of the expression (8): sizes and bounds are at least 1, `D ≤ N`, and from the threshold on
the hypotheses of Theorem 30 hold and `cost8P` and `L ∑ α_d` are at most `C tp` and `C tq`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX)
structure CostsWithinP (G : RatParams) (C : ℝ) (N D₀ : ℕ) (tp tq : ℝ) : Prop where
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
    cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N ≤ C * tp ∧
    costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) ≤ C * tq

variable {G : RatParams}

/-- For `m ≥ m₀` the hypotheses of Theorem 30 hold. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX.hyp)
theorem CostsWithinP.hyp {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithinP G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.Hyp N D₀ :=
  (h.above hm).1

/-- For `m ≥ m₀` the cost `cost8P` is at most `C tp`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX.pre_le)
theorem CostsWithinP.pre_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithinP G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : preCostP G N D₀ ≤ C * tp :=
  (h.above hm).2.1

/-- For `m ≥ m₀` the cost of a query is at most `C tq`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX.query_le)
theorem CostsWithinP.query_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithinP G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.queryCost D₀ ≤ C * tq :=
  (h.above hm).2.2

/-- The bound on a query, as upstream wants it: the expression (8) is dominated by itself. This
gives upstream's facts about queries, which do not involve (8). -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX.toCostsWithin)
theorem CostsWithinP.toCostsWithin {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ}
    (h : CostsWithinP G C N D₀ tp tq) :
    CostsWithin G (max C 1) N D₀ (max 1 (G.preCost N D₀)) tq := by
  refine ⟨h.one_le_N, h.one_le_D, h.D_le_N, le_max_left _ _, h.one_le_query, fun hm =>
    ⟨h.hyp hm, ?_, (h.query_le hm).trans ?_⟩⟩
  · exact (le_max_right 1 _).trans (le_mul_of_one_le_left (by positivity) (le_max_right C 1))
  · exact mul_le_mul_of_nonneg_right (le_max_left C 1) (zero_le_one.trans h.one_le_query)

/-- From the threshold on, `tPre31P` and `tPre31` differ only in the time of the core. -/
theorem tPre31P_add_tPreCore (c0 : ℕ) (N D₀ : ℕ) (hm : G.m₀ ≤ logFour D₀) :
    tPre31P c0 G N D₀ + tPreCore c0 (parOf G N D₀) (switchOf31 G D₀)
      = tPre31 c0 G N D₀ + tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) := by
  unfold tPre31P tPre31
  rw [if_neg (not_lt.2 hm), if_neg (not_lt.2 hm)]
  ring

/-- Setting up takes `O(L + N 4^m)` steps: upstream's `exists_tPre31_le_setup` for the pruned
preprocessing. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Costs.lean
-- (exists_tPre31_le_setup)
theorem exists_tPre31P_le_setup : ∃ k : ℕ, ∀ c0 N D₀ : ℕ, G.m₀ ≤ logFour D₀ →
    tPre31P c0 G N D₀ ≤ k * (G.L (logFour D₀) + 1 + N * 4 ^ logFour D₀ + N)
      + tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) := by
  obtain ⟨k, hk⟩ := exists_tPre31_le_setup G
  refine ⟨k, fun c0 N D₀ hm => ?_⟩
  have h1 := hk c0 N D₀ hm
  have h2 := tPre31P_add_tPreCore (G := G) c0 N D₀ hm
  omega

/-- From the threshold on the pruned preprocessing takes `O(cost8P)` steps. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (exists_tPre31_le_cost8X)
theorem exists_tPre31P_le_cost8P (G : RatParams) (c0 : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N D₀ : ℕ, 1 ≤ N →
    G.m₀ ≤ logFour D₀ → G.Hyp N D₀ → (tPre31P c0 G N D₀ : ℝ) ≤ K * preCostP G N D₀ := by
  obtain ⟨k, hk⟩ := exists_tPre31P_le_setup (G := G)
  obtain ⟨Cp, hCp0, hCp⟩ := exists_tPreCore_leP c0
  refine ⟨k * 4 + Cp, by positivity, fun N D₀ hN hm h => ?_⟩
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL0 : (0 : ℝ) ≤ (G.L (logFour D₀) : ℝ) := by positivity
  have hcore : (tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ)
      ≤ Cp * preCostP G N D₀ := hCp (parOf G N D₀) (switchOf31 G D₀) h
  have hNF : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ preCostP G N D₀ := N_mul_pow_le_cost8P h
  have hNL : (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) ≤ preCostP G N D₀ := N_mul_le_cost8P h
  have hsetup : (tPre31P c0 G N D₀ : ℝ)
      ≤ k * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
        + (tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ) := by exact_mod_cast hk c0 N D₀ hm
  -- L + 1 ≤ N (L + 1) and N ≤ N (L + 1), so that the sum is at most 4 times `cost8P`
  have hL : (G.L (logFour D₀) : ℝ) + 1 ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_left (by positivity) hN'
  have hNle : (N : ℝ) ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have hsum : (k : ℝ) * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
      ≤ k * (4 * preCostP G N D₀) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **The time of the pruned preprocessing** is at most a constant times every bound `tp ≥ 1`
that, from the threshold on, dominates `cost8P`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (exists_tPre31_leX)
theorem exists_tPre31P_le (G : RatParams) {C : ℝ} (hC : 0 ≤ C) (c0 : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithinP G C N D₀ tp tq → (tPre31P c0 G N D₀ : ℝ) ≤ A * tp := by
  obtain ⟨K, hK0, hK⟩ := exists_tPre31P_le_cost8P G c0
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((20 * G.m₀ + 50 : ℕ) : ℝ)) (by positivity) hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tp _ h.one_le_pre h.pre_le (fun hm => ?_) fun hm => ?_⟩
  · have hsmall : tPre31P c0 G N D₀ ≤ 20 * G.m₀ + 50 := by
      unfold tPre31P tLog4
      rw [if_pos hm]
      omega
    exact_mod_cast hsmall
  · have := hK N D₀ h.one_le_N hm (h.hyp hm)
    have : (0 : ℝ) ≤ ((20 * G.m₀ + 50 : ℕ) : ℝ) := by positivity
    linarith

/-- **The time of the pruned offline routine**, with `k` further steps, is at most a constant
times `tp + w tq`, for all bounds `tp, tq ≥ 1` that dominate `cost8P` and the cost of a query. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (exists_tOffline32_leX)
theorem exists_tOffline32P_le (G : RatParams) {C : ℝ} (hC : 0 ≤ C) (c0 k : ℕ) : ∃ A : ℝ,
    ∀ {N D₀ : ℕ} {tp tq : ℝ} (w : ℕ), CostsWithinP G C N D₀ tp tq →
      (tOffline32P c0 G N D₀ w : ℝ) + k ≤ A * (tp + w * tq) := by
  obtain ⟨Ap, hAp0, hAp⟩ := exists_tPre31P_le G hC c0
  obtain ⟨Aq, hAq0, hAq⟩ := exists_tQuery31_le G (hC.trans (le_max_left C 1))
  refine ⟨(Ap + 20 + k) + (Aq + 30), fun {N D₀ tp tq} w h => ?_⟩
  have hpre := hAp h
  have hquery := hAq h.toCostsWithin
  have htp := h.one_le_pre
  have htq := h.one_le_query
  have hw : (0 : ℝ) ≤ (w : ℝ) := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hwtq : 0 ≤ (w : ℝ) * tq := mul_nonneg hw (by linarith)
  have htime : (tOffline32P c0 G N D₀ w : ℝ)
      = (tPre31P c0 G N D₀ : ℝ) + (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) + 20 := by
    simp only [tOffline32P]
    push_cast
    ring
  -- the preprocessing and the k + 20 further steps against tp, the w queries against w tq
  have hfirst : (tPre31P c0 G N D₀ : ℝ) + 20 + k ≤ (Ap + 20 + k) * tp := by
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
