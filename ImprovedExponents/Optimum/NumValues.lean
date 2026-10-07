module

public import ImprovedExponents.Optimum.NumLog

@[expose] public section

/-!
# Certified values of the constants at `c = 107/5`, `c = 108/5` and `c = 22`

The values are computed with the toolkit of `Optimum/NumLog.lean`: every statement becomes an
inequality between rational numbers.

* `c = 108/5` is admissible for the paper's encodings, `18 ln 4 ≤ baseFull (108/5)`
  (`baseFull_ge_18`), and `basePruned (109/5) < 18 ln 4` (`basePruned_lt_18`).
* At `c = 108/5` with the paper's encodings: `Γ = 0.074835…` (`Gam_108_5_mem`) and the saving is
  `F = 0.0020597… > 0.00205` (`savingF_full_gt`, `savingF_full_lt`).
* At `c = 107/5` with the paper's encodings, near the maximum of the saving: `Γ = 0.0741367…`
  (`Gam_107_5_mem`) and the saving is `F = 0.00205990… > 0.002059` (`savingF_full_107_5_gt`,
  `savingF_full_107_5_lt`).
* At `c = 22` with pruned encodings: `Γ = 0.076207…` (`Gam_22_mem`, `Gam_22_bounds`), the thinness
  bound is `R = 0.054988…` (`thinR_pruned_bounds`) and the saving is `F = 0.0020952…`
  (`savingF_pruned_gt`, `savingF_pruned_lt`).
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

/-! ### The thinness constants -/

/-- `baseFull (108/5) = 25.0798… ≥ 18 ln 4 = 24.9533…`. -/
theorem baseFull_ge_18 : 18 * Real.log 4 ≤ baseFull (108 / 5) :=
  (mul_le_mul_of_nonneg_left logFour_mem.2 (by norm_num)).trans (le_baseFull 4)

/-- `basePruned (109/5) = 24.8805… < 18 ln 4 = 24.9533…`. -/
theorem basePruned_lt_18 : basePruned (109 / 5) < 18 * Real.log 4 :=
  (basePruned_le 4 : basePruned (109 / 5) ≤ 24.9).trans_lt
    (lt_of_lt_of_le (by numlog) (mul_le_mul_of_nonneg_left logFour_mem.1 (by norm_num)))

/-- `baseFull (108/5) = 25.07984…`. -/
theorem baseFull_108_5_mem : baseFull (108 / 5) ∈ Icc (25.0798 : ℝ) 25.0799 :=
  ⟨le_baseFull 4, baseFull_le 4⟩

/-- `baseFull (107/5) = 24.843803…`. -/
theorem baseFull_107_5_mem : baseFull (107 / 5) ∈ Icc (24.8438 : ℝ) 24.84381 :=
  ⟨le_baseFull 4, baseFull_le 4⟩

/-- `basePruned 22 = 25.104839…`. -/
theorem basePruned_22_mem : basePruned 22 ∈ Icc (25.10483 : ℝ) 25.10485 :=
  ⟨le_basePruned 4, basePruned_le 4⟩

/-! ### `c = 108/5` with the paper's encodings -/

/-- `Γ(108/5) = 0.0748357…`; the crossing is at `θ = 0.1163743…`. -/
theorem Gam_108_5_mem : Gam (108 / 5) ∈ Icc (0.074835 : ℝ) 0.074837 :=
  ⟨le_Gam (θ := 0.116374) (le_gammaX 4) (le_gammaQ (-3)),
    Gam_le (θ := 0.116375) (gammaX_le 4) (gammaQ_le (-3))⟩

/-- The saving at `c = 108/5` with the paper's encodings is more than `0.00205`
(it is `0.0020597…`). -/
theorem savingF_full_gt : (0.00205 : ℝ) < savingF (baseFull (108 / 5)) (Gam (108 / 5)) :=
  lt_savingF (baseFull_pos (by norm_num)) baseFull_108_5_mem.2 Gam_108_5_mem.1

/-- The saving at `c = 108/5` with the paper's encodings is less than `0.00206`. -/
theorem savingF_full_lt : savingF (baseFull (108 / 5)) (Gam (108 / 5)) < (0.00206 : ℝ) :=
  savingF_lt baseFull_108_5_mem.1 (Gam_pos (by norm_num)).le Gam_108_5_mem.2

/-- The thinness bound at `c = 108/5` with the paper's encodings is `R_c(Γ) = 0.055047…`. -/
theorem Rc_108_5_bounds : (0.05504 : ℝ) < Rc (108 / 5) (Gam (108 / 5)) ∧
    Rc (108 / 5) (Gam (108 / 5)) < (0.05505 : ℝ) := by
  rw [Rc_eq_thinR]
  exact ⟨lt_thinR (baseFull_pos (by norm_num)) baseFull_108_5_mem.2 (Gam_pos (by norm_num)).le
    Gam_108_5_mem.2, thinR_lt baseFull_108_5_mem.1 Gam_108_5_mem.1⟩

/-! ### `c = 107/5` with the paper's encodings -/

/-- `Γ(107/5) = 0.0741367…`; the crossing is at `θ = 0.1165464…`. -/
theorem Gam_107_5_mem : Gam (107 / 5) ∈ Icc (0.0741364 : ℝ) 0.0741372 :=
  ⟨le_Gam (θ := 0.116546) (le_gammaX 4) (le_gammaQ (-3)),
    Gam_le (θ := 0.116547) (gammaX_le 4) (gammaQ_le (-3))⟩

/-- The saving at `c = 107/5` with the paper's encodings is more than `0.002059`
(it is `0.00205990…`, within `10⁻⁹` of the maximum over `c`). -/
theorem savingF_full_107_5_gt : (0.002059 : ℝ) < savingF (baseFull (107 / 5)) (Gam (107 / 5)) :=
  lt_savingF (baseFull_pos (by norm_num)) baseFull_107_5_mem.2 Gam_107_5_mem.1

/-- The saving at `c = 107/5` with the paper's encodings is less than `0.00206`. -/
theorem savingF_full_107_5_lt : savingF (baseFull (107 / 5)) (Gam (107 / 5)) < (0.00206 : ℝ) :=
  savingF_lt baseFull_107_5_mem.1 (Gam_pos (by norm_num)).le Gam_107_5_mem.2

/-! ### `c = 22` with pruned encodings -/

/-- `Γ(22) = 0.0762079…`; the crossing is at `θ = 0.1160367…`. -/
theorem Gam_22_mem : Gam 22 ∈ Icc (0.076207 : ℝ) 0.076209 :=
  ⟨le_Gam (θ := 0.116036) (le_gammaX 4) (le_gammaQ (-3)),
    Gam_le (θ := 0.116037) (gammaX_le 4) (gammaQ_le (-3))⟩

/-- `0.0762 < Γ(22) < 0.0763`. -/
theorem Gam_22_bounds : (0.0762 : ℝ) < Gam 22 ∧ Gam 22 < (0.0763 : ℝ) :=
  ⟨lt_of_lt_of_le (by norm_num) Gam_22_mem.1, Gam_22_mem.2.trans_lt (by norm_num)⟩

/-- The thinness bound at `c = 22` with pruned encodings: `0.05498 < R(Γ) < 0.05499`
(it is `0.0549888…`). -/
theorem thinR_pruned_bounds : (0.05498 : ℝ) < thinR (basePruned 22) (Gam 22) ∧
    thinR (basePruned 22) (Gam 22) < (0.05499 : ℝ) :=
  ⟨lt_thinR (basePruned_pos (by norm_num)) basePruned_22_mem.2 (Gam_pos (by norm_num)).le
    Gam_22_mem.2, thinR_lt basePruned_22_mem.1 Gam_22_mem.1⟩

/-- The saving at `c = 22` with pruned encodings is more than `0.002095`
(it is `0.00209529…`). -/
theorem savingF_pruned_gt : (0.002095 : ℝ) < savingF (basePruned 22) (Gam 22) :=
  lt_savingF (basePruned_pos (by norm_num)) basePruned_22_mem.2 Gam_22_mem.1

/-- The saving at `c = 22` with pruned encodings is less than `0.002096`. -/
theorem savingF_pruned_lt : savingF (basePruned 22) (Gam 22) < (0.002096 : ℝ) :=
  savingF_lt basePruned_22_mem.1 (Gam_pos (by norm_num)).le Gam_22_mem.2

end ImprovedExponents
