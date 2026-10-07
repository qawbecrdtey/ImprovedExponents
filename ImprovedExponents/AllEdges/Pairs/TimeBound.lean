module

public import ImprovedExponents.AllEdges.Pairs.Host
public import ImprovedExponents.AllEdges.Chain

@[expose] public section

/-!
# The running time of pairsAE against a real bound

`pairsAE` (`ImprovedExponents.AllEdges.Pairs.Host`) makes `2b + 3` calls of a solver of all-edges
Exact Triangle at the bound `9U`, `b = aeLevels U = ⌊log₂ 3U⌋ + 1`, with `O(n²)` steps around
each call.  Against a real bound `T n u` on the solver, for `U ≤ u`, this is
`CA (1 + log u) (T(n, 9u) + n²)` with the explicit constant `CA`; `pairsFromAllEdges` delivers the
transfer `PairsFromAllEdges CA` that the chain `ImprovedExponents.AllEdges.Chain` consumes.
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/TimeBound.lean (mpRounds_le)
/-- The number of levels is `O(log u)`: `⌊log₂ 3U⌋ + 1 ≤ 3 (1 + logU u)` for `1 ≤ U ≤ u`. -/
theorem aeLevels_le {U : ℕ} (hU : 1 ≤ U) {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (aeLevels U : ℝ) ≤ 3 * (1 + logU u) := by
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hhalf := Real.one_half_lt_log_two
  have h2u := log_two_le_logU u
  have hpow : 2 ^ Nat.log 2 (3 * U) ≤ 3 * U := Nat.pow_log_le_self 2 (by omega)
  -- ⌊log₂ 3U⌋ log 2 ≤ log 3U = log 3 + log U ≤ 2 log 2 + log U
  have hlog : (Nat.log 2 (3 * U) : ℝ) * Real.log 2 ≤ Real.log (3 * U) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_four]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hUu : Real.log U ≤ logU u := (Real.log_le_log (by positivity) hu).trans
    (log_le_logU (by linarith))
  simp only [aeLevels]
  push_cast
  rcases le_or_gt (Nat.log 2 (3 * U)) 1 with hL | hL
  · have : (Nat.log 2 (3 * U) : ℝ) ≤ 1 := by exact_mod_cast hL
    linarith
  · -- (⌊log₂ 3U⌋ − 2) / 2 ≤ (⌊log₂ 3U⌋ − 2) log 2 ≤ log U ≤ logU u
    have hL2 : (0 : ℝ) ≤ (Nat.log 2 (3 * U) : ℝ) - 2 := by
      have : (2 : ℝ) ≤ Nat.log 2 (3 * U) := by exact_mod_cast hL
      linarith
    have hleft := mul_le_mul_of_nonneg_left hhalf.le hL2
    linarith

/-- The constant of the transfer from all-edges Exact Triangle to all pairs. -/
noncomputable def CA : ℝ := 2000

/-- The constant is nonnegative. -/
theorem CA_nonneg : 0 ≤ CA := by
  unfold CA
  norm_num

/-- **The time of pairsAE** against a real bound `T` on the solver of all-edges Exact Triangle:
`2b + 3 ≤ 9 (1 + log u)` calls, each with its `O(n²)` steps, and `O(n²)` steps at the start. -/
theorem pairsTimeAE_le {Tn : ℕ → ℕ → ℕ} {T : ℕ → ℝ → ℝ}
    (hT : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u)
    {n U : ℕ} {u : ℝ} (hn : 1 ≤ n) (hU : 1 ≤ U) (hu : (U : ℝ) ≤ u) :
    (pairsTimeAE Tn n U : ℝ) ≤ CA * ((1 + logU u) * (T n (9 * u) + (n : ℝ) ^ 2)) := by
  have hb := aeLevels_le hU hu
  have hL0 : (0 : ℝ) ≤ logU u := (logU_pos u).le
  have hTn := hT n (9 * U) (9 * u) hn (by omega) (by push_cast; linarith)
  have hT0 : (0 : ℝ) ≤ T n (9 * u) := (Nat.cast_nonneg _).trans hTn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  -- the number of calls, and the time of a call with its surroundings
  have hcalls : (2 * (aeLevels U : ℝ) + 3) ≤ 9 * (1 + logU u) := by linarith
  have hcall : (Tn n (9 * U) : ℝ) + 108 * (n : ℝ) ^ 2 + 60 ≤
      168 * (T n (9 * u) + (n : ℝ) ^ 2) := by linarith
  have hprod := mul_le_mul hcalls hcall (by positivity) (by positivity)
  -- the steps at the start
  have hstart : 350 * (T n (9 * u) + (n : ℝ) ^ 2) ≤
      350 * ((1 + logU u) * (T n (9 * u) + (n : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) (by linarith)) (by norm_num)
  have hsq : ((n : ℝ) * n) = (n : ℝ) ^ 2 := (sq (n : ℝ)).symm
  simp only [pairsTimeAE, CA]
  push_cast
  rw [hsq]
  nlinarith [hprod, hstart, hL0, hT0, hn1]

/-- **All pairs from all-edges Exact Triangle**, as the chain consumes it: a solver of all-edges
Exact Triangle in time `T` gives a solver of `pairsTask` in time
`CA (1 + log u) (T(n, 9u) + n²)`. -/
theorem pairsFromAllEdges : PairsFromAllEdges CA :=
  fun _ h => isHost_pairsAE.solvedIn h fun _ hTn _ _ _ hn hU hu => pairsTimeAE_le hTn hn hU hu

end ImprovedExponents.AllEdges
