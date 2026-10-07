module

public import ImprovedExponents.PrunedEncoding.Yates
public import ThreeSumApsp.Sec2.Orders

@[expose] public section

/-!
# Pruned encodings: the pruned Yates recursion and its operation count

The recursion of the paper reads the encodings `Φ_τ(a)` only at leaves `τ` with at most `m` symbols
`P₀` (`ThreeSumApsp.order_nonneg`), and the array `a` vanishes off the left strings with exactly
`m` inner variables. The pruned Yates recursion computes, at stage `k`, only the entries indexed by

  `stageSet L k m` = (strings of `k` terms with at most `m` symbols `P₀`)
                     × (strings of `L - k` left variables with at most `m` inner variables),

each as a sum over the at most three left variables `v` with `φ_τ(v) ≠ 0` of `φ_τ(v)` times an
entry of the previous stage (`prunedStage`). All other entries are treated as `0`.

* `card_stageSet_of_le`: `|stageSet L k m| = prefCount k m * sufCount (L - k) m`.
* `prunedStage_eq_yatesStage`: at the strings with at most `m` symbols `P₀`, the pruned arrays
  agree with those of Yates' algorithm; `prunedStage_final`: the last one holds `Φ_τ(a)`.
* `prunedMults L m` is the number of multiplications of the pruned recursion, that is, the number of
  summands of all the sums that define the entries of all stages. `prunedMults_le_M`: it is at most
  `(27/2) M/(1 - ρ)` for `10 m ≤ L`.
* `pruned_encoding`: the summary.
-/

namespace ImprovedExponents

open Finset ThreeSumApsp

/-- The index set `P_k × U_k` of stage `k` of the pruned recursion: the mixed strings with terms at
the levels below `k` and left variables from level `k` on, with at most `m` symbols `P₀` and at
most `m` inner variables. -/
def stageSet (L k m : ℕ) : Finset (MixStr L) :=
  univ.filter fun s => IsStage k s ∧ p0Count s ≤ m ∧ innerCount s ≤ m

/-- The left variables with a nonzero coefficient in the left form of a term (none for a symbol
that is not a term). -/
def coeffSupport : Term ⊕ LeftVar → Finset LeftVar
  | .inl τ => univ.filter fun v => phi τ v ≠ 0
  | .inr _ => ∅

/-- A left form has at most three nonzero coefficients. -/
theorem card_coeffSupport_le (x : Term ⊕ LeftVar) : (coeffSupport x).card ≤ 3 := by
  cases x with
  | inl τ => exact card_phi_ne_zero_le τ
  | inr v => simp [coeffSupport]

/-- **The pruned Yates recursion.** The array of stage `0` is `a` on `stageSet L 0 m`; an entry of
stage `k + 1` at a string of `stageSet L (k + 1) m` with the term `τ` at level `k` is the sum, over
the left variables `v` with `φ_τ(v) ≠ 0`, of `φ_τ(v)` times the entry of stage `k` at the string
with `v` in place of `τ`. The entries outside the sets `stageSet L k m` are `0` and are not
computed. -/
def prunedStage {L : ℕ} (m : ℕ) (a : LeftStr L → ℤ) : ℕ → MixStr L → ℤ
  | 0, s => if s ∈ stageSet L 0 m then a (rightPart s) else 0
  | k + 1, s =>
    if h : k < L then
      if s ∈ stageSet L (k + 1) m then
        ∑ v ∈ coeffSupport (s ⟨k, h⟩),
          mixCoeff (s ⟨k, h⟩) v * prunedStage m a k (Function.update s ⟨k, h⟩ (.inr v))
      else 0
    else prunedStage m a k s

/-- The number of multiplications of the pruned Yates recursion: the total number of summands of
the sums that define the entries of `prunedStage` at the strings of `stageSet L (ℓ + 1) m`, for the
levels `ℓ < L`. -/
def prunedMults (L m : ℕ) : ℕ :=
  ∑ ℓ : Fin L, ∑ s ∈ stageSet L (ℓ.val + 1) m, (coeffSupport (s ℓ)).card

/-- The sum that defines an entry of stage `k + 1` of the pruned recursion. -/
theorem prunedStage_succ {L m : ℕ} (a : LeftStr L → ℤ) {k : ℕ} (hk : k < L) {s : MixStr L}
    (hs : s ∈ stageSet L (k + 1) m) :
    prunedStage m a (k + 1) s = ∑ v ∈ coeffSupport (s ⟨k, hk⟩),
      mixCoeff (s ⟨k, hk⟩) v * prunedStage m a k (Function.update s ⟨k, hk⟩ (.inr v)) := by
  rw [prunedStage, dite_eq_left hk, ite_eq_left hs]

/-- The pruned array of stage `k` vanishes outside `stageSet L k m`. -/
theorem prunedStage_eq_zero {L m : ℕ} (a : LeftStr L → ℤ) {k : ℕ} (hk : k ≤ L) {s : MixStr L}
    (hs : s ∉ stageSet L k m) : prunedStage m a k s = 0 := by
  cases k with
  | zero => rw [prunedStage, ite_eq_right hs]
  | succ k => rw [prunedStage, dite_eq_left (by omega), ite_eq_right hs]

/-- The entries that the sum for an entry of stage `k + 1` reads: the string with a left variable
`v` in place of the term at level `k` has the shape of stage `k` and at most `m` symbols `P₀`, so
it lies in `stageSet L k m` unless it has more than `m` inner variables (and then the entry is a
known zero, by `prunedStage_eq_zero`). -/
theorem update_mem_stageSet_iff {L k m : ℕ} (hk : k < L) {s : MixStr L}
    (hs : s ∈ stageSet L (k + 1) m) (v : LeftVar) :
    Function.update s ⟨k, hk⟩ (.inr v) ∈ stageSet L k m
      ↔ innerCount (Function.update s ⟨k, hk⟩ (.inr v)) ≤ m := by
  obtain ⟨-, hst, hp, -⟩ := mem_filter.mp hs
  obtain ⟨τ, hτ⟩ := Sum.isLeft_iff.mp ((hst ⟨k, hk⟩).1 (Nat.lt_succ_self k))
  have h1 := (isStage_update_iff hk hτ v).mpr hst
  have h2 := (p0Count_update_le s ⟨k, hk⟩ v).trans hp
  exact ⟨fun h => (mem_filter.mp h).2.2.2, fun h => mem_filter.mpr ⟨mem_univ _, h1, h2, h⟩⟩

/-- If `a` vanishes off the left strings with exactly `m` inner variables, the arrays of Yates'
algorithm vanish at the strings with at most `m` symbols `P₀` outside `stageSet L k m`. -/
theorem yatesStage_eq_zero_of_notMem {L m : ℕ} {a : LeftStr L → ℤ}
    (ha : ∀ u, (innerSetL u).card ≠ m → a u = 0) {k : ℕ} {s : MixStr L} (hp : p0Count s ≤ m)
    (hs : s ∉ stageSet L k m) : yatesStage a k s = 0 := by
  by_cases h : IsStage k s
  · refine yatesStage_eq_zero_of_innerCount ha k ?_
    by_contra hcon
    exact hs (mem_filter.mpr ⟨mem_univ _, h, hp, by omega⟩)
  · exact yatesStage_eq_zero_of_not_isStage a h

/-- **The pruned recursion computes the arrays of Yates' algorithm** at all strings with at most
`m` symbols `P₀`, if `a` vanishes off the left strings with exactly `m` inner variables. -/
theorem prunedStage_eq_yatesStage {L m : ℕ} {a : LeftStr L → ℤ}
    (ha : ∀ u, (innerSetL u).card ≠ m → a u = 0) (k : ℕ) (s : MixStr L) (hp : p0Count s ≤ m) :
    prunedStage m a k s = yatesStage a k s := by
  induction k generalizing s with
  | zero =>
    rw [prunedStage]
    by_cases hs : s ∈ stageSet L 0 m
    · rw [ite_eq_left hs]
      exact (ite_eq_left (mem_filter.mp hs).2.1).symm
    · rw [ite_eq_right hs, yatesStage_eq_zero_of_notMem ha hp hs]
  | succ k ih =>
    rw [prunedStage]
    by_cases hk : k < L
    · rw [dite_eq_left hk]
      by_cases hs : s ∈ stageSet L (k + 1) m
      · rw [ite_eq_left hs]
        have hl := ((mem_filter.mp hs).2.1 ⟨k, hk⟩).1 (Nat.lt_succ_self k)
        obtain ⟨τ, hτ⟩ := Sum.isLeft_iff.mp hl
        rw [yatesStage_succ a hk hτ, hτ]
        have hsupp : coeffSupport (.inl τ) = univ.filter fun v => phi τ v ≠ 0 := rfl
        rw [hsupp, sum_filter_of_ne]
        · refine sum_congr rfl fun v _ => ?_
          rw [ih _ ((p0Count_update_le s _ v).trans hp)]
          rfl
        · intro v _ hv h0
          apply hv
          change phi τ v * _ = 0
          rw [h0, zero_mul]
      · rw [ite_eq_right hs, yatesStage_eq_zero_of_notMem ha hp hs]
    · rw [dite_eq_right hk, ih s hp, yatesStage, dite_eq_right hk]

/-- **The pruned recursion computes the encodings**: its last array holds `Φ_τ(a)` at every leaf
`τ` with at most `m` symbols `P₀`. -/
theorem prunedStage_final {L m : ℕ} {a : LeftStr L → ℤ}
    (ha : ∀ u, (innerSetL u).card ≠ m → a u = 0) (τ : Leaf L) (hτ : (P0Levels τ).card ≤ m) :
    prunedStage m a L (Sum.inl ∘ τ) = Phi τ a := by
  rw [prunedStage_eq_yatesStage ha L _ (by rw [p0Count_inl]; exact hτ), yatesStage_final]

/-- The pruned recursion computes the encodings at all the leaves that the recursion of the paper
reads: those of `Leaves U`, for a set `U` of output strings with inner sets of size `m`. -/
theorem prunedStage_final_of_mem_Leaves {L m : ℕ} {a : LeftStr L → ℤ}
    (ha : ∀ u, (innerSetL u).card ≠ m → a u = 0) {U : Finset (OutStr L)}
    (hU : ∀ w ∈ U, (innerSetO w).card = m) {τ : Leaf L} (hτ : τ ∈ Leaves U) :
    prunedStage m a L (Sum.inl ∘ τ) = Phi τ a := by
  obtain ⟨w, hw, hc⟩ := (mem_filter.mp hτ).2
  have h0 := order_nonneg (hU w hw) hc
  unfold order at h0
  exact prunedStage_final ha τ (by omega)

/-! ### The sizes of the index sets -/

/-- The mixed string of stage `k` made of a string of `k` terms and a string of left variables. -/
def mixAppend {k n : ℕ} (τ : Vertex k) (u : LeftStr n) : MixStr (k + n) :=
  Fin.append (Sum.inl ∘ τ) (Sum.inr ∘ u)

/-- The first `k` symbols of `mixAppend τ u` are the terms of `τ`. -/
theorem mixAppend_left {k n : ℕ} (τ : Vertex k) (u : LeftStr n) (i : Fin k) :
    mixAppend τ u (Fin.castAdd n i) = .inl (τ i) := by
  simp [mixAppend]

/-- The last `n` symbols of `mixAppend τ u` are the left variables of `u`. -/
theorem mixAppend_right {k n : ℕ} (τ : Vertex k) (u : LeftStr n) (j : Fin n) :
    mixAppend τ u (Fin.natAdd k j) = .inr (u j) := by
  simp [mixAppend]

/-- `mixAppend τ u` has the shape of stage `k`. -/
theorem isStage_mixAppend {k n : ℕ} (τ : Vertex k) (u : LeftStr n) :
    IsStage k (mixAppend τ u) := by
  intro ℓ
  induction ℓ using Fin.addCases with
  | left i =>
    rw [mixAppend_left]
    exact ⟨fun _ => rfl, fun h => by have h1 := i.isLt; have h2 : k ≤ i.val := h; omega⟩
  | right j =>
    rw [mixAppend_right]
    exact ⟨fun h => by have h2 : k + j.val < k := h; omega, fun _ => rfl⟩

/-- Every mixed string of the shape of stage `k` is some `mixAppend τ u`. -/
theorem exists_mixAppend_of_isStage {k n : ℕ} {s : MixStr (k + n)} (h : IsStage k s) :
    ∃ (τ : Vertex k) (u : LeftStr n), s = mixAppend τ u := by
  refine ⟨fun i => Sum.elim id (fun _ => Term.P0) (s (Fin.castAdd n i)),
    fun j => rightPart s (Fin.natAdd k j), ?_⟩
  funext ℓ
  induction ℓ using Fin.addCases with
  | left i =>
    rw [mixAppend_left]
    obtain ⟨t, ht⟩ := Sum.isLeft_iff.mp ((h (Fin.castAdd n i)).1 i.isLt)
    rw [ht]
    rfl
  | right j =>
    rw [mixAppend_right]
    obtain ⟨v, hv⟩ := Sum.isRight_iff.mp ((h (Fin.natAdd k j)).2 (Nat.le_add_right k j))
    unfold rightPart
    rw [hv]
    rfl

/-- `mixAppend` is injective. -/
theorem mixAppend_injective (k n : ℕ) :
    Function.Injective fun p : Vertex k × LeftStr n => mixAppend p.1 p.2 := by
  rintro ⟨τ, u⟩ ⟨τ', u'⟩ h
  have h1 : τ = τ' := by
    funext i
    have hi := congrFun h (Fin.castAdd n i)
    simpa only [mixAppend_left, Sum.inl.injEq] using hi
  have h2 : u = u' := by
    funext j
    have hj := congrFun h (Fin.natAdd k j)
    simpa only [mixAppend_right, Sum.inr.injEq] using hj
  rw [h1, h2]

/-- The symbols `P₀` of `mixAppend τ u` are those of `τ`. -/
theorem p0Count_mixAppend {k n : ℕ} (τ : Vertex k) (u : LeftStr n) :
    p0Count (mixAppend τ u) = (P0Levels τ).card := by
  unfold p0Count P0Levels
  rw [card_filter, card_filter, Fin.sum_univ_add]
  simp [mixAppend_left, mixAppend_right]

/-- The inner variables of `mixAppend τ u` are those of `u`. -/
theorem innerCount_mixAppend {k n : ℕ} (τ : Vertex k) (u : LeftStr n) :
    innerCount (mixAppend τ u) = (innerSetL u).card := by
  unfold innerCount innerSetL
  rw [card_filter, card_filter, Fin.sum_univ_add]
  simp [mixAppend_left, mixAppend_right]

/-- The index set of stage `k` is the product `P_k × U_k`. -/
theorem stageSet_eq_image (k n m : ℕ) :
    stageSet (k + n) k m
      = (termStrings k m ×ˢ leftStrings n m).image fun p => mixAppend p.1 p.2 := by
  ext s
  simp only [stageSet, mem_filter, mem_univ, true_and, mem_image, mem_product, termStrings,
    leftStrings, Prod.exists]
  constructor
  · rintro ⟨hst, hp, hi⟩
    obtain ⟨τ, u, rfl⟩ := exists_mixAppend_of_isStage hst
    rw [p0Count_mixAppend] at hp
    rw [innerCount_mixAppend] at hi
    exact ⟨τ, u, ⟨hp, hi⟩, rfl⟩
  · rintro ⟨τ, u, ⟨hτ, hu⟩, rfl⟩
    exact ⟨isStage_mixAppend τ u, by rwa [p0Count_mixAppend], by rwa [innerCount_mixAppend]⟩

/-- `|P_k × U_k| = prefCount k m * sufCount n m` for strings of length `k + n`. -/
theorem card_stageSet (k n m : ℕ) :
    (stageSet (k + n) k m).card = prefCount k m * sufCount n m := by
  rw [stageSet_eq_image, card_image_of_injective _ (mixAppend_injective k n), card_product,
    card_termStrings, card_leftStrings]

/-- **The size of the array of stage `k`**: `|P_k × U_k| = prefCount k m * sufCount (L - k) m`. -/
theorem card_stageSet_of_le {k L : ℕ} (hk : k ≤ L) (m : ℕ) :
    (stageSet L k m).card = prefCount k m * sufCount (L - k) m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, card_stageSet]

/-! ### The operation count -/

/-- **The number of array entries of the pruned Yates recursion**, over all stages, is at most
`(9/2) M/(1 - ρ)` for `10 m ≤ L`. -/
theorem sum_card_stageSet_le {L m : ℕ} (h : 10 * m ≤ L) :
    ∑ k ∈ range (L + 1), ((stageSet L k m).card : ℝ)
      ≤ 9 / 2 * (M L m : ℝ) / (1 - rho L m) := by
  refine le_trans (le_of_eq ?_) (sum_prefCount_mul_sufCount_le h)
  refine sum_congr rfl fun k hk => ?_
  rw [card_stageSet_of_le (Nat.lt_succ_iff.mp (mem_range.mp hk)) m, Nat.cast_mul]

/-- The pruned recursion performs at most `3 ∑_k |P_k| |U_k|` multiplications. -/
theorem prunedMults_le (L m : ℕ) :
    prunedMults L m ≤ 3 * ∑ k ∈ range (L + 1), prefCount k m * sufCount (L - k) m := by
  have h1 : prunedMults L m
      ≤ ∑ ℓ : Fin L, 3 * (prefCount (ℓ.val + 1) m * sufCount (L - (ℓ.val + 1)) m) := by
    unfold prunedMults
    refine sum_le_sum fun ℓ _ => ?_
    calc ∑ s ∈ stageSet L (ℓ.val + 1) m, (coeffSupport (s ℓ)).card
        ≤ (stageSet L (ℓ.val + 1) m).card • 3 :=
          sum_le_card_nsmul _ _ _ fun s _ => card_coeffSupport_le _
      _ = 3 * (prefCount (ℓ.val + 1) m * sufCount (L - (ℓ.val + 1)) m) := by
          rw [card_stageSet_of_le (Nat.succ_le_of_lt ℓ.isLt) m, smul_eq_mul, mul_comm]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => 3 * (prefCount (k + 1) m * sufCount (L - (k + 1)) m)) L] at h1
  rw [sum_range_succ', mul_add, mul_sum]
  exact h1.trans (Nat.le_add_right _ _)

/-- **The operation count of the pruned Yates recursion**: at most `(27/2) M/(1 - ρ)`
multiplications for `10 m ≤ L`, where `M = C(L, m) 9^{L-m}` and `ρ = 9m/(L - m + 1)`. -/
theorem prunedMults_le_M {L m : ℕ} (h : 10 * m ≤ L) :
    (prunedMults L m : ℝ) ≤ 27 / 2 * (M L m : ℝ) / (1 - rho L m) := by
  have h1 := (Nat.cast_le (α := ℝ)).mpr (prunedMults_le L m)
  push_cast at h1
  have h2 := sum_prefCount_mul_sufCount_le h
  have h3 : 27 / 2 * (M L m : ℝ) / (1 - rho L m) = 3 * (9 / 2 * (M L m : ℝ) / (1 - rho L m)) := by
    ring
  rw [h3]
  linarith

/-- **Lemma B (pruned encodings).** Let `10 m ≤ L` and let the array `a` on the left strings of
length `L` vanish off the strings with exactly `m` inner variables. The pruned Yates recursion
`prunedStage m a` computes the encoding `Φ_τ(a)` of every leaf `τ` with at most `m` symbols `P₀`;
its array of stage `k` is supported on `stageSet L k m`, a set of
`prefCount k m * sufCount (L - k) m` strings; each entry of that set at a stage `k + 1` is a sum of
`|coeffSupport τ| ≤ 3` products of a coefficient `±1` and an entry of stage `k`; the total number
of entries of these sets is at most `(9/2) M/(1 - ρ)`; and the total number of these products is at
most `(27/2) M/(1 - ρ)`. -/
theorem pruned_encoding {L m : ℕ} (h : 10 * m ≤ L) {a : LeftStr L → ℤ}
    (ha : ∀ u, (innerSetL u).card ≠ m → a u = 0) :
    (∀ τ : Leaf L, (P0Levels τ).card ≤ m → prunedStage m a L (Sum.inl ∘ τ) = Phi τ a) ∧
    (∀ k ≤ L, ∀ s ∉ stageSet L k m, prunedStage m a k s = 0) ∧
    (∀ k ≤ L, (stageSet L k m).card = prefCount k m * sufCount (L - k) m) ∧
    (∀ (k : ℕ) (hk : k < L), ∀ s ∈ stageSet L (k + 1) m,
      prunedStage m a (k + 1) s = ∑ v ∈ coeffSupport (s ⟨k, hk⟩),
        mixCoeff (s ⟨k, hk⟩) v * prunedStage m a k (Function.update s ⟨k, hk⟩ (.inr v)) ∧
      (coeffSupport (s ⟨k, hk⟩)).card ≤ 3) ∧
    ∑ k ∈ range (L + 1), ((stageSet L k m).card : ℝ) ≤ 9 / 2 * (M L m : ℝ) / (1 - rho L m) ∧
    (prunedMults L m : ℝ) ≤ 27 / 2 * (M L m : ℝ) / (1 - rho L m) :=
  ⟨fun τ hτ => prunedStage_final ha τ hτ,
    fun _ hk _ hs => prunedStage_eq_zero a hk hs,
    fun _ hk => card_stageSet_of_le hk m,
    fun _ hk _ hs => ⟨prunedStage_succ a hk hs, card_coeffSupport_le _⟩,
    sum_card_stageSet_le h, prunedMults_le_M h⟩

end ImprovedExponents
