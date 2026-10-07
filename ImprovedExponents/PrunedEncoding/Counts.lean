module

public import PaperStatements

@[expose] public section

/-!
# Pruned encodings: the sizes of the staged arrays

The encodings `Φ_τ(a)` of an array `a` on the left strings of length `L` are computed by Yates'
algorithm, one level at a time. The pruned algorithm keeps, at stage `k`, only the entries indexed
by a string of `k` terms with at most `m` symbols `P₀` followed by a string of `L - k` left
variables with at most `m` inner variables. This file has the numbers of such strings,

* `prefCount k m = ∑_{j ≤ m} C(k, j) 9^{k-j}` and
* `sufCount n m = ∑_{i ≤ m} C(n, i) 4^i 3^{n-i}`,

and the bounds on them: `9 prefCount k m ≤ prefCount (k+1) m`, `sufCount (n+1) m ≤ 7 sufCount n m`,
hence `∑_k prefCount k m * sufCount (L-k) m ≤ (9/2) prefCount L m`, and
`prefCount L m ≤ M/(1 - ρ)` for `10 m ≤ L`, where `M = C(L, m) 9^{L-m}` and `ρ = 9m/(L-m+1)`.
-/

namespace ImprovedExponents

open Finset ThreeSumApsp

/-- `prefCount k m = ∑_{j ≤ m} C(k, j) 9^{k-j}`: the number of strings of `k` terms with at most
`m` symbols `P₀` (see `card_termStrings`). -/
def prefCount (k m : ℕ) : ℕ := ∑ j ∈ range (m + 1), k.choose j * 9 ^ (k - j)

/-- `sufCount n m = ∑_{i ≤ m} C(n, i) 4^i 3^{n-i}`: the number of strings of `n` left variables
with at most `m` inner variables (see `card_leftStrings`). -/
def sufCount (n m : ℕ) : ℕ := ∑ i ∈ range (m + 1), n.choose i * 4 ^ i * 3 ^ (n - i)

/-- A string of terms that is longer by one symbol can be chosen in at least `9` times as many
ways: `9 |P_k| ≤ |P_{k+1}|`. -/
theorem nine_mul_prefCount_le (k m : ℕ) : 9 * prefCount k m ≤ prefCount (k + 1) m := by
  unfold prefCount
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  rcases Nat.lt_or_ge k j with hj | hj
  · simp [Nat.choose_eq_zero_of_lt hj]
  · have h1 : k + 1 - j = (k - j) + 1 := by omega
    rw [h1, pow_succ]
    nlinarith [Nat.choose_le_succ k j, Nat.zero_le (9 ^ (k - j)),
      Nat.mul_le_mul_right (9 ^ (k - j)) (Nat.choose_le_succ k j)]

/-- Pascal's rule for the terms of `sufCount`. -/
theorem sufCount_term_succ (n i : ℕ) :
    (n + 1).choose (i + 1) * 4 ^ (i + 1) * 3 ^ (n + 1 - (i + 1))
      = 4 * (n.choose i * 4 ^ i * 3 ^ (n - i))
        + 3 * (n.choose (i + 1) * 4 ^ (i + 1) * 3 ^ (n - (i + 1))) := by
  rw [Nat.choose_succ_succ, Nat.add_sub_add_right]
  rcases Nat.lt_or_ge i n with hi | hi
  · have h1 : n - i = (n - (i + 1)) + 1 := by omega
    rw [h1]
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < i + 1)]
    ring

/-- A string of left variables that is longer by one symbol can be chosen in at most `7` times as
many ways: `|U_k| ≤ 7 |U_{k+1}|`. -/
theorem sufCount_succ_le (n m : ℕ) : sufCount (n + 1) m ≤ 7 * sufCount n m := by
  have h : sufCount (n + 1) m
      = 3 * sufCount n m + 4 * ∑ i ∈ range m, n.choose i * 4 ^ i * 3 ^ (n - i) := by
    unfold sufCount
    rw [sum_range_succ', sum_congr rfl fun i _ => sufCount_term_succ n i, sum_add_distrib,
      ← mul_sum, ← mul_sum, sum_range_succ' _ m]
    simp only [Nat.choose_zero_right, pow_zero, Nat.sub_zero, mul_one, one_mul]
    ring
  have h2 : ∑ i ∈ range m, n.choose i * 4 ^ i * 3 ^ (n - i) ≤ sufCount n m := by
    unfold sufCount
    exact sum_le_sum_of_subset (range_mono (Nat.le_succ m))
  omega

/-- There is one empty string. -/
theorem sufCount_zero (m : ℕ) : sufCount 0 m = 1 := by
  unfold sufCount
  rw [sum_range_succ']
  simp

/-- `|U| ≤ 7^n` for the strings of `n` left variables. -/
theorem sufCount_le_pow (n m : ℕ) : sufCount n m ≤ 7 ^ n := by
  induction n with
  | zero => simp [sufCount_zero]
  | succ n ih => calc
      sufCount (n + 1) m ≤ 7 * sufCount n m := sufCount_succ_le n m
      _ ≤ 7 * 7 ^ n := by gcongr
      _ = 7 ^ (n + 1) := by ring

/-- `9^d |P_k| ≤ |P_{k+d}|`. -/
theorem pow_mul_prefCount_le (k d m : ℕ) : 9 ^ d * prefCount k m ≤ prefCount (k + d) m := by
  induction d with
  | zero => simp
  | succ d ih => calc
      9 ^ (d + 1) * prefCount k m = 9 * (9 ^ d * prefCount k m) := by ring
      _ ≤ 9 * prefCount (k + d) m := by gcongr
      _ ≤ prefCount (k + d + 1) m := nine_mul_prefCount_le _ _

/-- The size of the stage `k` array is at most `(7/9)^{L-k}` times that of the last one:
`|P_k| |U_k| 9^{L-k} ≤ 7^{L-k} |P_L|`. -/
theorem prefCount_mul_sufCount_le {k L : ℕ} (hk : k ≤ L) (m : ℕ) :
    prefCount k m * sufCount (L - k) m * 9 ^ (L - k) ≤ 7 ^ (L - k) * prefCount L m := by
  have h1 := pow_mul_prefCount_le k (L - k) m
  rw [Nat.add_sub_cancel' hk] at h1
  calc prefCount k m * sufCount (L - k) m * 9 ^ (L - k)
      = sufCount (L - k) m * (9 ^ (L - k) * prefCount k m) := by ring
    _ ≤ 7 ^ (L - k) * prefCount L m := Nat.mul_le_mul (sufCount_le_pow _ _) h1

/-- The geometric sum `∑_{d < n} (7/9)^d = (9/2) (1 - (7/9)^n)`. -/
theorem geom_sum_seven_ninths (n : ℕ) :
    ∑ d ∈ range n, ((7 : ℚ) / 9) ^ d = 9 / 2 * (1 - (7 / 9) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

/-- The total size of the staged arrays is at most `9/2` times the size of the last one:
`2 ∑_{k ≤ L} |P_k| |U_k| ≤ 9 |P_L|`. -/
theorem two_mul_sum_prefCount_mul_sufCount_le (L m : ℕ) :
    2 * ∑ k ∈ range (L + 1), prefCount k m * sufCount (L - k) m ≤ 9 * prefCount L m := by
  have hterm : ∀ k ∈ range (L + 1), ((prefCount k m * sufCount (L - k) m : ℕ) : ℚ)
      ≤ (7 / 9) ^ (L - k) * prefCount L m := by
    intro k hk
    have h := prefCount_mul_sufCount_le (Nat.lt_succ_iff.mp (mem_range.mp hk)) m
    have h' : ((prefCount k m * sufCount (L - k) m : ℕ) : ℚ) * 9 ^ (L - k)
        ≤ 7 ^ (L - k) * prefCount L m := by exact_mod_cast h
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact h'
  have hsum : ∑ k ∈ range (L + 1), ((7 : ℚ) / 9) ^ (L - k) ≤ 9 / 2 := by
    have := sum_range_reflect (fun d => ((7 : ℚ) / 9) ^ d) (L + 1)
    simp only [Nat.add_sub_cancel] at this
    rw [this, geom_sum_seven_ninths]
    have : (0 : ℚ) ≤ (7 / 9) ^ (L + 1) := by positivity
    linarith
  have hq : (2 : ℚ) * ((∑ k ∈ range (L + 1), prefCount k m * sufCount (L - k) m : ℕ) : ℚ)
      ≤ 9 * prefCount L m := by
    rw [Nat.cast_sum]
    calc (2 : ℚ) * ∑ k ∈ range (L + 1), ((prefCount k m * sufCount (L - k) m : ℕ) : ℚ)
        ≤ 2 * ∑ k ∈ range (L + 1), (7 / 9 : ℚ) ^ (L - k) * prefCount L m := by
          gcongr with k hk
          exact hterm k hk
      _ = 2 * ((∑ k ∈ range (L + 1), (7 / 9 : ℚ) ^ (L - k)) * prefCount L m) := by
          rw [sum_mul]
      _ ≤ 2 * (9 / 2 * prefCount L m) := by gcongr
      _ = 9 * prefCount L m := by ring
  exact_mod_cast hq

/-- The last term of `prefCount L m` is `M = C(L, m) 9^{L-m}`. -/
theorem M_eq_choose_mul (L m : ℕ) : M L m = L.choose m * 9 ^ (L - m) := by
  unfold M K N0
  rw [← pow_mul, mul_comm (L - m) 2, pow_mul]
  norm_num

/-- The ratio of consecutive terms of `prefCount L m`:
`(L - j) C(L, j) 9^{L-j} = 9 (j+1) C(L, j+1) 9^{L-(j+1)}`. -/
theorem prefCount_term_ratio (L j : ℕ) :
    (L - j) * (L.choose j * 9 ^ (L - j))
      = 9 * (j + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := by
  rcases Nat.lt_or_ge j L with hj | hj
  · have h1 : L - j = (L - (j + 1)) + 1 := by omega
    have h2 := Nat.choose_succ_right_eq L j
    rw [h1, pow_succ, ← h1]
    calc (L - j) * (L.choose j * (9 ^ (L - (j + 1)) * 9))
        = 9 * (L.choose j * (L - j)) * 9 ^ (L - (j + 1)) := by ring
      _ = 9 * (L.choose (j + 1) * (j + 1)) * 9 ^ (L - (j + 1)) := by rw [h2]
      _ = 9 * (j + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := by ring
  · rw [Nat.sub_eq_zero_of_le hj, Nat.choose_eq_zero_of_lt (by omega : L < j + 1)]
    simp

/-- The terms of `prefCount L m` decay at rate `ρ = 9m/(L-m+1)` below the last one, so the sum is
at most `1/(1 - ρ)` times the last term. Without fractions:
`(L - m + 1 - 9m) ∑_{i ≤ j} C(L, i) 9^{L-i} ≤ (L - m + 1) C(L, j) 9^{L-j}` for `j ≤ m`. -/
theorem sub_mul_prefCount_le_aux (L m : ℕ) (h : 9 * m ≤ L - m + 1) :
    ∀ j ≤ m, (L - m + 1 - 9 * m) * prefCount L j ≤ (L - m + 1) * (L.choose j * 9 ^ (L - j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [prefCount, zero_add, range_one, sum_singleton]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    have hratio := prefCount_term_ratio L j
    have hstep : (L - m + 1) * (L.choose j * 9 ^ (L - j))
        ≤ 9 * m * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := calc
      (L - m + 1) * (L.choose j * 9 ^ (L - j)) ≤ (L - j) * (L.choose j * 9 ^ (L - j)) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 9 * (j + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := hratio
      _ ≤ 9 * m * (L.choose (j + 1) * 9 ^ (L - (j + 1))) :=
        Nat.mul_le_mul_right _ (by omega)
    have hsplit : prefCount L (j + 1)
        = prefCount L j + L.choose (j + 1) * 9 ^ (L - (j + 1)) := by
      unfold prefCount
      rw [sum_range_succ]
    rw [hsplit, mul_add]
    calc (L - m + 1 - 9 * m) * prefCount L j
          + (L - m + 1 - 9 * m) * (L.choose (j + 1) * 9 ^ (L - (j + 1)))
        ≤ 9 * m * (L.choose (j + 1) * 9 ^ (L - (j + 1)))
          + (L - m + 1 - 9 * m) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) :=
          Nat.add_le_add_right (ih'.trans hstep) _
      _ = (L - m + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := by
          rw [← add_mul, Nat.add_sub_cancel' h]

/-- `|P_L| ≤ M/(1 - ρ)` without fractions: `(L - m + 1 - 9m) |P_L| ≤ (L - m + 1) M` for
`10 m ≤ L`. (Here `L - m + 1 - 9m` is positive.) -/
theorem sub_mul_prefCount_le {L m : ℕ} (h : 10 * m ≤ L) :
    (L - m + 1 - 9 * m) * prefCount L m ≤ (L - m + 1) * M L m := by
  rw [M_eq_choose_mul]
  exact sub_mul_prefCount_le_aux L m (by omega) m le_rfl

/-- `ρ < 1` for `10 m ≤ L`. -/
theorem rho_lt_one {L m : ℕ} (h : 10 * m ≤ L) : rho L m < 1 := by
  have h' : (10 : ℝ) * m ≤ L := by exact_mod_cast h
  unfold rho
  rw [div_lt_one (by linarith)]
  linarith

/-- `|P_L| ≤ M/(1 - ρ)` for `10 m ≤ L`: the number of leaves with at most `m` symbols `P₀`. -/
theorem prefCount_le_M_div {L m : ℕ} (h : 10 * m ≤ L) :
    (prefCount L m : ℝ) ≤ (M L m : ℝ) / (1 - rho L m) := by
  have h' : (10 : ℝ) * m ≤ L := by exact_mod_cast h
  have hnat := sub_mul_prefCount_le h
  have hcast : ((L : ℝ) - m + 1 - 9 * m) * prefCount L m ≤ ((L : ℝ) - m + 1) * M L m := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_sub (by omega)]
      at this
    simpa using this
  have hpos : (0 : ℝ) < (L : ℝ) - m + 1 := by linarith
  have hrho : 1 - rho L m = ((L : ℝ) - m + 1 - 9 * m) / ((L : ℝ) - m + 1) := by
    unfold rho
    field_simp
  rw [hrho, div_div_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

/-- **The total size of the staged arrays of the pruned Yates recursion** is at most
`(9/2) M/(1 - ρ)` for `10 m ≤ L`. -/
theorem sum_prefCount_mul_sufCount_le {L m : ℕ} (h : 10 * m ≤ L) :
    ∑ k ∈ range (L + 1), ((prefCount k m : ℝ) * (sufCount (L - k) m : ℝ))
      ≤ 9 / 2 * (M L m : ℝ) / (1 - rho L m) := by
  have h1 := (Nat.cast_le (α := ℝ)).mpr (two_mul_sum_prefCount_mul_sufCount_le L m)
  push_cast at h1
  have h2 := prefCount_le_M_div h
  rw [mul_div_assoc]
  linarith

end ImprovedExponents
