module

public import ThreeSumApsp.Programs.Sec4.Theorem30.TimeOfBlock
public import ImprovedExponents.Cost8X.Defs
import all ThreeSumApsp.Programs.Sec4.Theorem30.Time

@[expose] public section

/-!
# The preprocessing of Theorem 30 runs within `cost8X`

Upstream shows that the preprocessing of Theorem 30 takes at most a constant times the expression
(8) (`Light.Sec4.exists_tPreCore_le`), through the predicate `Light.Sec4.Within8`, which names
`ThreeSumApsp.cost8`. This file repeats that analysis against `cost8X`, the expression with the
exact tail of the leaf counts: `Within8X`, and `exists_tPreCore_leX`. The program and its time
function `tPreCore` are upstream's.

The statements and proofs are adapted from upstream
`ThreeSumApsp/Programs/Sec4/Theorem30/Time.lean` and `TimeOfBlock.lean` (Apache-2.0). Only
`within8X_bands` and `within8X_boxes` use a different count (`cost8X_assembly`). The time of one
tile is upstream's private `exists_tTile_le`, which does not involve (8).
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec4 Finset

open private exists_tTile_le from ThreeSumApsp.Programs.Sec4.Theorem30.Time

/-- `10^L` is within `cost8X`: it is at most the last term. -/
theorem ten_pow_le_cost8X {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (10 : ℝ) ^ p.L ≤ cost8X p.L p.m t p.N := by
  have hfirst := cost8X_first_term_nonneg p.L p.m t p.N
  have hlast := Theorem30.subsets_absorbed h.L_ge h.N_ge
  unfold cost8X
  linarith

/-- `cost8X` is at least 1. -/
theorem one_le_cost8X (L m t N : ℕ) (hL : 10 * m ≤ L) (hN : sqrtKN0 L m ≤ (N : ℝ)) :
    1 ≤ cost8X L m t N := by
  have hfirst := cost8X_first_term_nonneg L m t N
  have hlast := Theorem30.subsets_absorbed hL hN
  have hone : (1 : ℝ) ≤ (10 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  unfold cost8X
  linarith

/-- `f = O(cost8X)`: at most a constant times `cost8X`, for all parameters that satisfy the
hypotheses of Theorem 30. -/
def Within8X (f : Sec2.Par → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, Hyp30 p t → (f p t : ℝ) ≤ C * cost8X p.L p.m t p.N

namespace Within8X

variable {f g : Sec2.Par → ℕ → ℕ}

/-- A smaller function. -/
theorem of_le (hg : Within8X g) (h : ∀ p t, Hyp30 p t → f p t ≤ g p t) : Within8X f :=
  let ⟨C, hC, hg⟩ := hg
  ⟨C, hC, fun p t hp => le_trans (by exact_mod_cast h p t hp) (hg p t hp)⟩

/-- A sum. -/
theorem add (hf : Within8X f) (hg : Within8X g) : Within8X fun p t => f p t + g p t := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  refine ⟨A + B, add_nonneg hA hB, fun p t hp => ?_⟩
  rw [Nat.cast_add, add_mul]
  exact add_le_add (hf p t hp) (hg p t hp)

/-- A multiple. -/
theorem const_mul (c : ℕ) (hf : Within8X f) : Within8X fun p t => c * f p t := by
  obtain ⟨A, hA, hf⟩ := hf
  refine ⟨c * A, by positivity, fun p t hp => ?_⟩
  rw [Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf p t hp) (Nat.cast_nonneg c)

end Within8X

/-- The number 1 is within `cost8X`. -/
theorem within8X_one : Within8X fun _ _ => 1 :=
  ⟨1, zero_le_one, fun p t h => by simpa using one_le_cost8X p.L p.m t p.N h.L_ge h.N_ge⟩

/-- The number `10^L` of leaves is within `cost8X`. -/
theorem within8X_ten_pow : Within8X fun p _ => 10 ^ p.L :=
  ⟨1, zero_le_one, fun p t h => by simpa using ten_pow_le_cost8X h⟩

/-- The work for the bands: `10^L + L 7^L` for each band. -/
theorem within8X_bands : Within8X fun p _ => p.nB * (10 ^ p.L + p.L * 7 ^ p.L) := by
  refine ⟨13 / 2, by norm_num, fun p t h => ?_⟩
  have hsum := cost8X_assembly h.m_pos h.L_ge h.t_le h.N_ge
  have hboxes :
      0 ≤ (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * ((boxes p.L p.m t).card : ℝ)) := by
    positivity
  have htable : 0 ≤ (K p.L p.m : ℝ) * (p.L : ℝ) := by positivity
  push_cast
  change (numBands p.L p.m p.N : ℝ) * _ ≤ _
  linarith

/-- The work for the boxes: `L` for each box of each tile. -/
theorem within8X_boxes : Within8X fun p t => p.L * (p.nB ^ 2 * (boxes p.L p.m t).card) := by
  refine ⟨13, by norm_num, fun p t h => ?_⟩
  have hsum := cost8X_assembly h.m_pos h.L_ge h.t_le h.N_ge
  have hbands :
      0 ≤ 2 * (numBands p.L p.m p.N : ℝ) * ((10 : ℝ) ^ p.L + (p.L : ℝ) * (7 : ℝ) ^ p.L) := by
    positivity
  have htable : 0 ≤ (K p.L p.m : ℝ) * (p.L : ℝ) := by positivity
  push_cast
  change (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * _) ≤ _
  linarith

/-- **The tries of all tiles** are built within `cost8X`. -/
theorem within8X_tAllTiles : Within8X fun p t => tAllTiles p.L p.m t p.nB := by
  obtain ⟨c, hc⟩ := exists_tTile_le
  refine ((within8X_boxes.const_mul c).add (within8X_one.const_mul 30)).of_le fun p t h => ?_
  have htile := hc p.L p.m t h.L_pos h.m_le
  have hn : p.nB ≤ p.nB ^ 2 := Nat.le_self_pow (by norm_num) _
  calc tAllTiles p.L p.m t p.nB
      = p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB * 40 + 30 := by simp only [tAllTiles]; ring
    _ ≤ p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB ^ 2 * 40 + 30 := by gcongr
    _ = p.nB ^ 2 * (tTile p.L p.m t + 120) + 30 := by ring
    _ ≤ p.nB ^ 2 * (c * (p.L * (boxes p.L p.m t).card)) + 30 := by gcongr
    _ = c * (p.L * (p.nB ^ 2 * (boxes p.L p.m t).card)) + 30 * 1 := by ring

/-- `N (L + 1)` is within three times `cost8X`, because `√K N₀ ≤ 7^L` and
`(L + 1) 7^L ≤ 3 · 10^L`. -/
theorem N_mul_le_cost8X {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * ((p.L : ℝ) + 1) ≤ 3 * cost8X p.L p.m t p.N := by
  have hpos := sqrtKN0_pos h.m_le
  have hfirst := cost8X_first_term_nonneg p.L p.m t p.N
  have hKN : (K p.L p.m : ℝ) * (N0 p.L p.m : ℝ) ≤ (7 : ℝ) ^ p.L := by
    exact_mod_cast le_trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by norm_num)))
      (Theorem30.K_mul_N0_mul_D_le p.L p.m)
  have htile : sqrtKN0 p.L p.m ≤ (7 : ℝ) ^ p.L := (sqrtKN0_le h.m_le).trans hKN
  have hseven : ((p.L : ℝ) + 1) * (7 : ℝ) ^ p.L ≤ 3 * (10 : ℝ) ^ p.L := by
    have harray := Theorem30.form_array p.L
    have hpow : 7 ^ p.L ≤ 10 ^ p.L := Nat.pow_le_pow_left (by norm_num) p.L
    exact_mod_cast (by rw [Nat.add_one_mul]; omega : (p.L + 1) * 7 ^ p.L ≤ 3 * 10 ^ p.L)
  have hlast : (p.N : ℝ) * ((p.L : ℝ) + 1)
      ≤ 3 * ((p.N : ℝ) * (10 : ℝ) ^ p.L / sqrtKN0 p.L p.m) := by
    rw [← mul_div_assoc, le_div_iff₀ hpos]
    calc (p.N : ℝ) * ((p.L : ℝ) + 1) * sqrtKN0 p.L p.m
        ≤ (p.N : ℝ) * ((p.L : ℝ) + 1) * (7 : ℝ) ^ p.L :=
          mul_le_mul_of_nonneg_left htile (by positivity)
      _ = (p.N : ℝ) * (((p.L : ℝ) + 1) * (7 : ℝ) ^ p.L) := by ring
      _ ≤ (p.N : ℝ) * (3 * (10 : ℝ) ^ p.L) := mul_le_mul_of_nonneg_left hseven (Nat.cast_nonneg _)
      _ = 3 * ((p.N : ℝ) * (10 : ℝ) ^ p.L) := by ring
  unfold cost8X
  linarith

/-- `N 4^m` is within `cost8X`: it is at most the last term, because
`√K N₀ 4^m ≤ K N₀ 4^m ≤ 7^L ≤ 10^L`. -/
theorem N_mul_pow_le_cost8X {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ cost8X p.L p.m t p.N := by
  have hfirst := cost8X_first_term_nonneg p.L p.m t p.N
  have hKND : K p.L p.m * N0 p.L p.m * 4 ^ p.m ≤ 10 ^ p.L :=
    (Theorem30.K_mul_N0_mul_D_le p.L p.m).trans (Nat.pow_le_pow_left (by norm_num) _)
  have hlast : (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ (p.N : ℝ) * (10 : ℝ) ^ p.L / sqrtKN0 p.L p.m := by
    rw [le_div_iff₀ (sqrtKN0_pos h.m_le), mul_assoc]
    gcongr
    calc (4 : ℝ) ^ p.m * sqrtKN0 p.L p.m
        ≤ (4 : ℝ) ^ p.m * ((K p.L p.m : ℝ) * (N0 p.L p.m : ℝ)) := by
          gcongr
          exact sqrtKN0_le h.m_le
      _ = ((K p.L p.m * N0 p.L p.m * 4 ^ p.m : ℕ) : ℝ) := by
          push_cast
          ring
      _ ≤ (10 : ℝ) ^ p.L := by exact_mod_cast hKND
  unfold cost8X
  linarith

/-- `N (L + 1)` is within `cost8X`. -/
theorem within8X_N_mul : Within8X fun p _ => p.N * (p.L + 1) :=
  ⟨3, by norm_num, fun p t h => by
    push_cast
    exact N_mul_le_cost8X h⟩

/-- The three quantities that bound the shared stage, together. -/
theorem within8X_shared :
    Within8X fun p _ => 10 ^ p.L + p.N * (p.L + 1) + p.nB * (10 ^ p.L + p.L * 7 ^ p.L) :=
  (within8X_ten_pow.add within8X_N_mul).add within8X_bands

/-- **The shared stage** runs within `cost8X`. -/
theorem within8X_sharedShape : Within8X fun p _ => Sec2.sharedShape p := by
  refine (within8X_shared.const_mul 12).of_le fun p t h => ?_
  have hshape := sharedShape_le p h.L_pos h.m_le
  have hLT : p.L + 1 ≤ 10 ^ p.L :=
    (Nat.le_self_pow (by norm_num) _).trans (succ_sq_le_ten_pow p.L)
  rw [Nat.add_one_mul p.N, ← Nat.mul_assoc, Nat.mul_comm p.nB 3, Nat.mul_assoc] at hshape
  omega

/-- **The preprocessing** takes `O(cost8X)` steps. `c` is the constant of the shared stage. -/
theorem exists_tPreCore_leX (c : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tPreCore c p t : ℝ) ≤ C * cost8X p.L p.m t p.N :=
  (((within8X_sharedShape.const_mul c).add within8X_tAllTiles).add
    (within8X_one.const_mul 300)).of_le fun _ _ _ => le_of_eq (by simp [tPreCore])

end ImprovedExponents
