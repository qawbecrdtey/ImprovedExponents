module

public import ImprovedExponents.MinPlus.Comparison
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

/-!
# Min-plus products by Exact Triangle, through comparisons as equalities

Let `A`, `B` be `n × n` integer matrices with entries of absolute value at most `W`, and let `t` be
a matrix of thresholds. By `add_lt_iff_shiftDiff`, applied to `x = A i k + W`, `y = B k j + W` and
`u = t i j + 2W`, the question "is there a `k` with `A i k + B k j < t i j`?" is, for all pairs
`(i, j)` at once, the disjunction of `2b + 3` Exact Triangle questions "is there a `k` with
`wIK i k + wKJ k j + wJI j i = 0`?" (`exists_lt_iff_exists_exactTriangle`). The instances are
indexed by the pairs `(ℓ, r)` of `lemmaFInstances b`: `r = 1` at `ℓ = 0`, and `r ∈ {2, 3}` at each
`ℓ ≤ b`; the weights are `etIK`, `etKJ` and `etJI`.

The entries of the min-plus product `C i j = min_k (A i k + B k j)` (`minPlus`) are found from
these answers by a binary search that runs for all pairs in parallel: `search` makes `R` rounds
when `4W + 1 ≤ 2^R`, each round asking one matrix of thresholds (`search_eq_minPlus`,
`search_exactTriangle`).
-/

namespace ImprovedExponents

open Finset

variable {n : ℕ}

/-! ### The Exact Triangle instances -/

/-- The weight of the edge `(i, k)` in the instance of level `ℓ`: `⌊(A i k + W)/2^ℓ⌋`. -/
def etIK (A : Fin n → Fin n → ℤ) (W ℓ : ℕ) (i k : Fin n) : ℤ := (A i k + W) / 2 ^ ℓ

/-- The weight of the edge `(k, j)` in the instance of level `ℓ`: `⌊(B k j + W)/2^ℓ⌋`. -/
def etKJ (B : Fin n → Fin n → ℤ) (W ℓ : ℕ) (k j : Fin n) : ℤ := (B k j + W) / 2 ^ ℓ

/-- The weight of the edge `(j, i)` in the instance `(ℓ, r)`: `r - ⌊(t i j + 2W)/2^ℓ⌋`. -/
def etJI (t : Fin n → Fin n → ℤ) (W ℓ : ℕ) (r : ℤ) (j i : Fin n) : ℤ :=
  r - (t i j + 2 * W) / 2 ^ ℓ

/-- The instances `(ℓ, r)`: `(0, 1)`, and `(ℓ, 2)` and `(ℓ, 3)` for `ℓ ≤ b`. -/
def lemmaFInstances (b : ℕ) : Finset (ℕ × ℤ) := insert (0, 1) (range (b + 1) ×ˢ {2, 3})

/-- There are `2b + 3` instances. -/
theorem card_lemmaFInstances (b : ℕ) : (lemmaFInstances b).card = 2 * b + 3 := by
  unfold lemmaFInstances
  rw [card_insert_of_notMem (by simp), card_product, card_range, card_pair (by norm_num)]
  ring

/-- In an instance `(ℓ, r)`, `1 ≤ r ≤ 3`. -/
theorem mem_lemmaFInstances_snd {b : ℕ} {c : ℕ × ℤ} (hc : c ∈ lemmaFInstances b) :
    1 ≤ c.2 ∧ c.2 ≤ 3 := by
  obtain ⟨ℓ, r⟩ := c
  simp only [lemmaFInstances, mem_insert, Prod.mk.injEq, mem_product, mem_range,
    mem_singleton] at hc
  rcases hc with ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩ <;> norm_num

/-- The disjunction of Lemma F as a statement about the instances. -/
theorem exists_mem_lemmaFInstances_iff (b : ℕ) (f : ℕ → ℤ) :
    (∃ c ∈ lemmaFInstances b, f c.1 = c.2) ↔ f 0 = 1 ∨ ∃ ℓ ≤ b, f ℓ = 2 ∨ f ℓ = 3 := by
  constructor
  · rintro ⟨⟨ℓ, r⟩, hc, hf⟩
    simp only [lemmaFInstances, mem_insert, Prod.mk.injEq, mem_product, mem_range,
      mem_singleton] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨hℓ, rfl | rfl⟩
    · exact Or.inl hf
    · exact Or.inr ⟨ℓ, by omega, Or.inl hf⟩
    · exact Or.inr ⟨ℓ, by omega, Or.inr hf⟩
  · rintro (h | ⟨ℓ, hℓ, h | h⟩)
    · exact ⟨(0, 1), mem_insert_self _ _, h⟩
    · exact ⟨(ℓ, 2), mem_insert_of_mem (mem_product.mpr ⟨mem_range.mpr (by omega), by simp⟩), h⟩
    · exact ⟨(ℓ, 3), mem_insert_of_mem (mem_product.mpr ⟨mem_range.mpr (by omega), by simp⟩), h⟩

/-- Lemma F for integers `p, q` of absolute value at most `W` and a threshold `t` with
`0 ≤ t + 2W < 2^b`, where `2W < 2^b`. -/
theorem lt_iff_exists_instance {b W : ℕ} {p q t : ℤ} (hp : |p| ≤ W) (hq : |q| ≤ W)
    (hW : 2 * W < 2 ^ b) (ht : -(2 * W : ℤ) ≤ t) (ht' : t + 2 * W < 2 ^ b) :
    p + q < t ↔ ∃ c ∈ lemmaFInstances b,
      (p + W) / 2 ^ c.1 + (q + W) / 2 ^ c.1 + (c.2 - (t + 2 * W) / 2 ^ c.1) = 0 := by
  have hp' := abs_le.mp hp
  have hq' := abs_le.mp hq
  have hW' : (2 * W : ℤ) < 2 ^ b := by exact_mod_cast hW
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le (by linarith : 0 ≤ p + W)
  obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le (by linarith : 0 ≤ q + W)
  obtain ⟨u, hu⟩ := Int.eq_ofNat_of_zero_le (by linarith : 0 ≤ t + 2 * W)
  have hxb : x < 2 ^ b := by
    have : (x : ℤ) < 2 ^ b := by rw [← hx]; linarith
    exact_mod_cast this
  have hyb : y < 2 ^ b := by
    have : (y : ℤ) < 2 ^ b := by rw [← hy]; linarith
    exact_mod_cast this
  have hub : u < 2 ^ b := by
    have : (u : ℤ) < 2 ^ b := by rw [← hu]; exact ht'
    exact_mod_cast this
  have hdiv : ∀ z ℓ : ℕ, (z : ℤ) / 2 ^ ℓ = ((z / 2 ^ ℓ : ℕ) : ℤ) := fun z ℓ => by norm_cast
  have hlt : p + q < t ↔ x + y < u := by omega
  rw [hlt, add_lt_iff_shiftDiff hxb hyb hub, ← exists_mem_lemmaFInstances_iff, hx, hy, hu]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [hdiv, hdiv, hdiv]
  unfold shiftDiff
  constructor <;> intro h <;> linarith

/-- **Lemma F for matrices: threshold questions as Exact Triangle instances.** Let `A`, `B` have
entries of absolute value at most `W`, let `2W < 2^b`, and let the thresholds satisfy
`-2W ≤ t i j` and `t i j + 2W < 2^b`. Then there is a `k` with `A i k + B k j < t i j` if and only
if, in one of the `2b + 3` instances `(ℓ, r)`, there is a `k` whose triangle `i, k, j` has weight
`0`. The weights of an instance depend on `(A, ℓ)`, `(B, ℓ)` and `(t, ℓ, r)` only. -/
theorem exists_lt_iff_exists_exactTriangle (A B t : Fin n → Fin n → ℤ) {W b : ℕ}
    (hA : ∀ i k, |A i k| ≤ W) (hB : ∀ k j, |B k j| ≤ W) (hW : 2 * W < 2 ^ b)
    (ht : ∀ i j, -(2 * W : ℤ) ≤ t i j ∧ t i j + 2 * W < 2 ^ b) (i j : Fin n) :
    (∃ k, A i k + B k j < t i j) ↔ ∃ c ∈ lemmaFInstances b,
      ∃ k, etIK A W c.1 i k + etKJ B W c.1 k j + etJI t W c.1 c.2 j i = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨c, hc, h⟩ :=
      (lt_iff_exists_instance (hA i k) (hB k j) hW (ht i j).1 (ht i j).2).mp hk
    exact ⟨c, hc, k, h⟩
  · rintro ⟨c, hc, k, h⟩
    exact ⟨k, (lt_iff_exists_instance (hA i k) (hB k j) hW (ht i j).1 (ht i j).2).mpr
      ⟨c, hc, h⟩⟩

/-- The same for thresholds in `[-2W, 2W + 1]`, the range that a search for the entries of the
min-plus product needs, with `4W + 2 ≤ 2^b`. -/
theorem exists_lt_iff_exists_exactTriangle_of_range (A B t : Fin n → Fin n → ℤ) {W b : ℕ}
    (hA : ∀ i k, |A i k| ≤ W) (hB : ∀ k j, |B k j| ≤ W) (hb : 4 * W + 2 ≤ 2 ^ b)
    (ht : ∀ i j, -(2 * W : ℤ) ≤ t i j ∧ t i j ≤ 2 * W + 1) (i j : Fin n) :
    (∃ k, A i k + B k j < t i j) ↔ ∃ c ∈ lemmaFInstances b,
      ∃ k, etIK A W c.1 i k + etKJ B W c.1 k j + etJI t W c.1 c.2 j i = 0 := by
  have hb' : (4 * W + 2 : ℤ) ≤ 2 ^ b := by exact_mod_cast hb
  exact exists_lt_iff_exists_exactTriangle A B t hA hB (by omega)
    (fun i j => ⟨(ht i j).1, by have := (ht i j).2; linarith⟩) i j

/-- A number in `[0, 2^b)` stays there when divided by a power of two. -/
theorem ediv_two_pow_bounds {z : ℤ} {b : ℕ} (h0 : 0 ≤ z) (hb : z < 2 ^ b) (ℓ : ℕ) :
    0 ≤ z / 2 ^ ℓ ∧ z / 2 ^ ℓ < 2 ^ b :=
  ⟨Int.ediv_nonneg h0 (by positivity), (Int.ediv_le_self _ h0).trans_lt hb⟩

/-- The weights `etIK` lie in `[0, 2^b)`. -/
theorem etIK_bounds {A : Fin n → Fin n → ℤ} {W b : ℕ} (hA : ∀ i k, |A i k| ≤ W)
    (hW : 2 * W < 2 ^ b) (ℓ : ℕ) (i k : Fin n) : 0 ≤ etIK A W ℓ i k ∧ etIK A W ℓ i k < 2 ^ b := by
  have h := abs_le.mp (hA i k)
  have hW' : (2 * W : ℤ) < 2 ^ b := by exact_mod_cast hW
  exact ediv_two_pow_bounds (by linarith) (by linarith) ℓ

/-- The weights `etKJ` lie in `[0, 2^b)`. -/
theorem etKJ_bounds {B : Fin n → Fin n → ℤ} {W b : ℕ} (hB : ∀ k j, |B k j| ≤ W)
    (hW : 2 * W < 2 ^ b) (ℓ : ℕ) (k j : Fin n) : 0 ≤ etKJ B W ℓ k j ∧ etKJ B W ℓ k j < 2 ^ b := by
  have h := abs_le.mp (hB k j)
  have hW' : (2 * W : ℤ) < 2 ^ b := by exact_mod_cast hW
  exact ediv_two_pow_bounds (by linarith) (by linarith) ℓ

/-- The weights `etJI` of an instance lie in `(-2^b, 3]`. -/
theorem etJI_bounds {t : Fin n → Fin n → ℤ} {W b : ℕ}
    (ht : ∀ i j, -(2 * W : ℤ) ≤ t i j ∧ t i j + 2 * W < 2 ^ b) {c : ℕ × ℤ}
    (hc : c ∈ lemmaFInstances b) (j i : Fin n) :
    -(2 ^ b : ℤ) < etJI t W c.1 c.2 j i ∧ etJI t W c.1 c.2 j i ≤ 3 := by
  have h := ediv_two_pow_bounds (by linarith [(ht i j).1] : 0 ≤ t i j + 2 * W) (ht i j).2 c.1
  have hr := mem_lemmaFInstances_snd hc
  unfold etJI
  constructor <;> linarith [h.1, h.2, hr.1, hr.2]

/-- All weights of all instances have absolute value at most `2^b + 3`. -/
theorem abs_weights_le {A B t : Fin n → Fin n → ℤ} {W b : ℕ} (hA : ∀ i k, |A i k| ≤ W)
    (hB : ∀ k j, |B k j| ≤ W) (hW : 2 * W < 2 ^ b)
    (ht : ∀ i j, -(2 * W : ℤ) ≤ t i j ∧ t i j + 2 * W < 2 ^ b) {c : ℕ × ℤ}
    (hc : c ∈ lemmaFInstances b) (i j k : Fin n) :
    |etIK A W c.1 i k| ≤ 2 ^ b + 3 ∧ |etKJ B W c.1 k j| ≤ 2 ^ b + 3
      ∧ |etJI t W c.1 c.2 j i| ≤ 2 ^ b + 3 := by
  have h1 := etIK_bounds hA hW c.1 i k
  have h2 := etKJ_bounds hB hW c.1 k j
  have h3 := etJI_bounds ht hc j i
  have hpos : (0 : ℤ) < 2 ^ b := by positivity
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith

/-! ### The min-plus product and the binary search -/

/-- The min-plus product: `C i j = min_k (A i k + B k j)`. -/
def minPlus [NeZero n] (A B : Fin n → Fin n → ℤ) (i j : Fin n) : ℤ :=
  univ.inf' univ_nonempty fun k => A i k + B k j

/-- The threshold question asks whether the entry of the min-plus product is below the
threshold. -/
theorem exists_lt_iff_minPlus_lt [NeZero n] (A B : Fin n → Fin n → ℤ) (i j : Fin n) (c : ℤ) :
    (∃ k, A i k + B k j < c) ↔ minPlus A B i j < c := by
  unfold minPlus
  rw [inf'_lt_iff]
  simp

/-- **The entry of the min-plus product from threshold questions**: `C i j` is the unique integer
`c` with a negative answer for the threshold `c` and a positive answer for the threshold `c + 1`. -/
theorem minPlus_unique [NeZero n] (A B : Fin n → Fin n → ℤ) (i j : Fin n) (c : ℤ) :
    ((¬ ∃ k, A i k + B k j < c) ∧ ∃ k, A i k + B k j < c + 1) ↔ c = minPlus A B i j := by
  rw [exists_lt_iff_minPlus_lt, exists_lt_iff_minPlus_lt]
  omega

/-- The entries of the min-plus product lie in `[-2W, 2W]`. -/
theorem minPlus_mem_range [NeZero n] {A B : Fin n → Fin n → ℤ} {W : ℕ}
    (hA : ∀ i k, |A i k| ≤ W) (hB : ∀ k j, |B k j| ≤ W) (i j : Fin n) :
    -(2 * W : ℤ) ≤ minPlus A B i j ∧ minPlus A B i j ≤ 2 * W := by
  constructor
  · refine le_inf' _ _ fun k _ => ?_
    linarith [(abs_le.mp (hA i k)).1, (abs_le.mp (hB k j)).1]
  · refine (inf'_le _ (mem_univ (0 : Fin n))).trans ?_
    linarith [(abs_le.mp (hA i 0)).2, (abs_le.mp (hB 0 j)).2]

/-- One round of the parallel binary search with `r` rounds to go: ask the thresholds
`lo i j + 2^r` for all pairs at once, and keep `lo i j` where the answer is positive. -/
def searchRound (q : (Fin n → Fin n → ℤ) → Fin n → Fin n → Bool) (r : ℕ)
    (lo : Fin n → Fin n → ℤ) : Fin n → Fin n → ℤ :=
  fun i j => if q (fun i j => lo i j + 2 ^ r) i j then lo i j else lo i j + 2 ^ r

/-- The parallel binary search with `r` rounds, from the lower bounds `lo`, with the oracle `q`
for threshold questions. Each round calls `q` once, on one matrix of thresholds. -/
def search (q : (Fin n → Fin n → ℤ) → Fin n → Fin n → Bool) :
    ℕ → (Fin n → Fin n → ℤ) → Fin n → Fin n → ℤ
  | 0, lo => lo
  | r + 1, lo => search q r (searchRound q r lo)

/-- The invariant of the binary search: if `lo i j ≤ C i j < lo i j + 2^r` and the oracle answers
correctly on thresholds `t` with `-2W ≤ t i j` and `t i j + 2W < 2^R`, the search with `r` rounds
returns the min-plus product, provided that `-2W ≤ lo i j` and `lo i j + 2^r ≤ -2W + 2^R`. -/
theorem search_eq_minPlus_aux [NeZero n] (A B : Fin n → Fin n → ℤ) (W R : ℕ)
    (q : (Fin n → Fin n → ℤ) → Fin n → Fin n → Bool)
    (hq : ∀ t : Fin n → Fin n → ℤ, (∀ i j, -(2 * W : ℤ) ≤ t i j ∧ t i j + 2 * W < 2 ^ R) →
      ∀ i j, (q t i j = true ↔ ∃ k, A i k + B k j < t i j)) :
    ∀ (r : ℕ) (lo : Fin n → Fin n → ℤ),
      (∀ i j, -(2 * W : ℤ) ≤ lo i j ∧ lo i j + 2 ^ r ≤ -(2 * W : ℤ) + 2 ^ R) →
      (∀ i j, lo i j ≤ minPlus A B i j ∧ minPlus A B i j < lo i j + 2 ^ r) →
      search q r lo = minPlus A B := by
  intro r
  induction r with
  | zero =>
    intro lo _ h
    funext i j
    have := h i j
    rw [pow_zero] at this
    rw [search]
    omega
  | succ r ih =>
    intro lo hlo h
    rw [search]
    have hpos : (0 : ℤ) < 2 ^ r := by positivity
    have hpow : (2 : ℤ) ^ (r + 1) = 2 * 2 ^ r := by ring
    have hask := hq (fun i j => lo i j + 2 ^ r) fun i j => by
      have := hlo i j
      rw [hpow] at this
      constructor <;> linarith
    refine ih _ (fun i j => ?_) (fun i j => ?_)
    · have := hlo i j
      rw [hpow] at this
      unfold searchRound
      split_ifs <;> constructor <;> linarith
    · have := h i j
      rw [hpow] at this
      have hiff := (hask i j).trans (exists_lt_iff_minPlus_lt A B i j _)
      unfold searchRound
      by_cases hc : q (fun i j => lo i j + 2 ^ r) i j = true
      · rw [ite_eq_left hc]
        have := hiff.mp hc
        constructor <;> linarith
      · rw [ite_eq_right hc]
        have hge : lo i j + 2 ^ r ≤ minPlus A B i j := not_lt.mp fun hlt => hc (hiff.mpr hlt)
        constructor <;> linarith

/-- **The parallel binary search computes the min-plus product** in `R` rounds when
`4W + 1 ≤ 2^R`, each round asking one matrix of thresholds `t` with `-2W ≤ t i j` and
`t i j + 2W < 2^R`; the oracle needs to be correct on such thresholds only. -/
theorem search_eq_minPlus [NeZero n] (A B : Fin n → Fin n → ℤ) {W R : ℕ}
    (hA : ∀ i k, |A i k| ≤ W) (hB : ∀ k j, |B k j| ≤ W) (hR : 4 * W + 1 ≤ 2 ^ R)
    (q : (Fin n → Fin n → ℤ) → Fin n → Fin n → Bool)
    (hq : ∀ t : Fin n → Fin n → ℤ, (∀ i j, -(2 * W : ℤ) ≤ t i j ∧ t i j + 2 * W < 2 ^ R) →
      ∀ i j, (q t i j = true ↔ ∃ k, A i k + B k j < t i j)) :
    search q R (fun _ _ => -(2 * W : ℤ)) = minPlus A B := by
  have hR' : (4 * W + 1 : ℤ) ≤ 2 ^ R := by exact_mod_cast hR
  refine search_eq_minPlus_aux A B W R q hq R _ (fun i j => ⟨le_rfl, le_rfl⟩) fun i j => ?_
  have := minPlus_mem_range hA hB i j
  constructor <;> linarith

/-- The number of rounds `R = ⌈log₂ (4W + 2)⌉` suffices. -/
theorem four_mul_add_one_le_two_pow_clog (W : ℕ) : 4 * W + 1 ≤ 2 ^ Nat.clog 2 (4 * W + 2) :=
  (Nat.le_succ _).trans (Nat.le_pow_clog (by norm_num) _)

/-- **The min-plus product by Exact Triangle.** With `R` rounds, `4W + 1 ≤ 2^R`, the parallel
binary search whose threshold questions are answered by the `2R + 3` Exact Triangle instances of
`lemmaFInstances R` computes the min-plus product of two matrices with entries of absolute value
at most `W`. -/
theorem search_exactTriangle [NeZero n] (A B : Fin n → Fin n → ℤ) {W R : ℕ}
    (hA : ∀ i k, |A i k| ≤ W) (hB : ∀ k j, |B k j| ≤ W) (hR : 4 * W + 1 ≤ 2 ^ R) :
    search (fun t i j => decide (∃ c ∈ lemmaFInstances R,
        ∃ k, etIK A W c.1 i k + etKJ B W c.1 k j + etJI t W c.1 c.2 j i = 0))
      R (fun _ _ => -(2 * W : ℤ)) = minPlus A B := by
  refine search_eq_minPlus A B hA hB hR _ fun t ht i j => ?_
  rw [decide_eq_true_iff]
  exact (exists_lt_iff_exists_exactTriangle A B t hA hB (by omega) ht i j).symm

/-- The min-plus product by Exact Triangle in `R = ⌈log₂ (4W + 2)⌉` rounds. -/
theorem search_exactTriangle_clog [NeZero n] (A B : Fin n → Fin n → ℤ) {W R : ℕ}
    (hA : ∀ i k, |A i k| ≤ W) (hB : ∀ k j, |B k j| ≤ W) (hR : R = Nat.clog 2 (4 * W + 2)) :
    search (fun t i j => decide (∃ c ∈ lemmaFInstances R,
        ∃ k, etIK A W c.1 i k + etKJ B W c.1 k j + etJI t W c.1 c.2 j i = 0))
      R (fun _ _ => -(2 * W : ℤ)) = minPlus A B :=
  search_exactTriangle A B hA hB (hR ▸ four_mul_add_one_le_two_pow_clog W)

end ImprovedExponents
