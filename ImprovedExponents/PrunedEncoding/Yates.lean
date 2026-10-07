module

public import ImprovedExponents.PrunedEncoding.Card

@[expose] public section

/-!
# Pruned encodings: Yates' algorithm, stage by stage

The encodings `Φ_τ(a) = ∑_u a[u] ∏_ℓ φ_{τ_ℓ}(u_ℓ)` of an array `a` on the left strings of length `L`
are computed one level at a time. Stage `k` holds the array

  `A_k[τ_1 ⋯ τ_k ; u_{k+1} ⋯ u_L] = ∑_{u_1, …, u_k} a[u] ∏_{ℓ ≤ k} φ_{τ_ℓ}(u_ℓ)`,

so that `A_0 = a` and `A_L[τ] = Φ_τ(a)`. Its index is a *mixed string*: terms at the first `k`
levels and left variables at the others. We let all the arrays live on the mixed strings
`Fin L → Term ⊕ LeftVar` (`MixStr L`), an array of stage `k` vanishing outside the strings of that
shape (`IsStage k`).

* `yatesStep ℓ` is the step at level `ℓ`, and `yatesStage a k` is the array after the steps at the
  levels `0, …, k - 1`, starting from `yatesInit a`.
* `yatesStage_eq`: the entries are the partial encodings `mixPhi a s`.
* `yatesStage_final`: the last array holds the encodings `Phi τ a`.
* `yatesStage_eq_zero_of_innerCount`: if `a` vanishes off the strings with exactly `m` inner
  variables, an entry with more than `m` inner variables among its left variables is `0`.
* `yatesStage_succ`, `p0Count_update_le`, `card_phi_ne_zero_le`: an entry of stage `k + 1` is a sum
  of at most three entries of stage `k`, with signs, whose strings have no more symbols `P₀`.
-/

namespace ImprovedExponents

open Finset ThreeSumApsp

/-- A mixed string of length `L`: at each level, a term or a left variable. -/
abbrev MixStr (L : ℕ) : Type := Fin L → Term ⊕ LeftVar

/-- The coefficient of a left variable `v` at one level of a mixed string: `φ_τ(v)` at a term `τ`,
and `[v = v']` at a left variable `v'`. -/
def mixCoeff : Term ⊕ LeftVar → LeftVar → ℤ
  | .inl τ, v => phi τ v
  | .inr v', v => if v = v' then 1 else 0

/-- The partial encoding of an array `a` for a mixed string `s`: the sum of `a[u] ∏ φ_{τ_ℓ}(u_ℓ)`,
the product over the levels `ℓ` at which `s` has a term `τ_ℓ`, over the left strings `u` that
agree with `s` at the other levels. -/
def mixPhi {L : ℕ} (a : LeftStr L → ℤ) (s : MixStr L) : ℤ :=
  ∑ u, a u * ∏ ℓ, mixCoeff (s ℓ) (u ℓ)

/-- The shape of the indices of stage `k`: terms at the levels below `k`, left variables at the
levels from `k` on. -/
def IsStage {L : ℕ} (k : ℕ) (s : MixStr L) : Prop :=
  ∀ ℓ : Fin L, (ℓ.val < k → (s ℓ).isLeft) ∧ (k ≤ ℓ.val → (s ℓ).isRight)

/-- The shape of stage `k` is decidable. -/
instance {L : ℕ} (k : ℕ) : DecidablePred (IsStage (L := L) k) := fun s =>
  inferInstanceAs
    (Decidable (∀ ℓ : Fin L, (ℓ.val < k → (s ℓ).isLeft) ∧ (k ≤ ℓ.val → (s ℓ).isRight)))

/-- The left variables of a mixed string (with `x₁` at the levels where it has a term). -/
def rightPart {L : ℕ} (s : MixStr L) : LeftStr L :=
  fun ℓ => Sum.elim (fun _ => LeftVar.x 0) id (s ℓ)

/-- The array of stage `0`: `A_0[u] = a[u]`, and `0` at the mixed strings that have a term. -/
def yatesInit {L : ℕ} (a : LeftStr L → ℤ) (s : MixStr L) : ℤ :=
  if IsStage 0 s then a (rightPart s) else 0

/-- The step of Yates' algorithm at level `ℓ`:
`A'[… τ …] = ∑_v φ_τ(v) A[… v …]`, the term `τ` and the left variable `v` at level `ℓ`. The new
array vanishes at the strings that have a left variable at level `ℓ`. -/
def yatesStep {L : ℕ} (ℓ : Fin L) (A : MixStr L → ℤ) (s : MixStr L) : ℤ :=
  match s ℓ with
  | .inl τ => ∑ v, phi τ v * A (Function.update s ℓ (.inr v))
  | .inr _ => 0

/-- The array of stage `k`: the steps at the levels `0, …, k - 1` applied to `yatesInit a`. -/
def yatesStage {L : ℕ} (a : LeftStr L → ℤ) : ℕ → MixStr L → ℤ
  | 0 => yatesInit a
  | k + 1 => if h : k < L then yatesStep ⟨k, h⟩ (yatesStage a k) else yatesStage a k

/-- The number of symbols `P₀` of a mixed string. -/
def p0Count {L : ℕ} (s : MixStr L) : ℕ := (univ.filter fun ℓ => s ℓ = .inl Term.P0).card

/-- The number of inner left variables of a mixed string. -/
def innerCount {L : ℕ} (s : MixStr L) : ℕ :=
  (univ.filter fun ℓ => ∃ v, s ℓ = .inr v ∧ v.IsInner).card

/-- The step at a string with a term at level `ℓ`. -/
theorem yatesStep_inl {L : ℕ} (ℓ : Fin L) (A : MixStr L → ℤ) {s : MixStr L} {τ : Term}
    (h : s ℓ = .inl τ) :
    yatesStep ℓ A s = ∑ v, phi τ v * A (Function.update s ℓ (.inr v)) := by
  unfold yatesStep
  rw [h]

/-- The step at a string with a left variable at level `ℓ`. -/
theorem yatesStep_inr {L : ℕ} (ℓ : Fin L) (A : MixStr L → ℤ) {s : MixStr L} {v : LeftVar}
    (h : s ℓ = .inr v) : yatesStep ℓ A s = 0 := by
  unfold yatesStep
  rw [h]

/-- A sum over the left variable at one level of partial encodings. -/
theorem sum_mul_mixPhi_update {L : ℕ} (a : LeftStr L → ℤ) (s : MixStr L) (ℓ₀ : Fin L)
    (c : LeftVar → ℤ) :
    ∑ v, c v * mixPhi a (Function.update s ℓ₀ (.inr v))
      = ∑ u, a u * (c (u ℓ₀) * ∏ ℓ ∈ univ.erase ℓ₀, mixCoeff (s ℓ) (u ℓ)) := by
  have hprod : ∀ (v : LeftVar) (u : LeftStr L),
      ∏ ℓ, mixCoeff (Function.update s ℓ₀ (.inr v) ℓ) (u ℓ)
        = (if u ℓ₀ = v then 1 else 0) * ∏ ℓ ∈ univ.erase ℓ₀, mixCoeff (s ℓ) (u ℓ) := by
    intro v u
    rw [← mul_prod_erase univ _ (mem_univ ℓ₀), Function.update_self]
    congr 1
    refine prod_congr rfl fun ℓ hℓ => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hℓ)]
  unfold mixPhi
  simp only [hprod, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_eq_single (u ℓ₀)]
  · rw [if_pos rfl]
    ring
  · intro v _ hv
    rw [if_neg (Ne.symm hv)]
    ring
  · intro h
    exact absurd (mem_univ _) h

/-- One step of Yates' algorithm, for the partial encodings. -/
theorem sum_phi_mul_mixPhi_update {L : ℕ} (a : LeftStr L → ℤ) (s : MixStr L) (ℓ₀ : Fin L)
    {τ : Term} (h : s ℓ₀ = .inl τ) :
    ∑ v, phi τ v * mixPhi a (Function.update s ℓ₀ (.inr v)) = mixPhi a s := by
  rw [sum_mul_mixPhi_update]
  unfold mixPhi
  refine sum_congr rfl fun u _ => ?_
  rw [← mul_prod_erase univ _ (mem_univ ℓ₀), h]
  rfl

/-- The partial encoding for a string of left variables is the entry of the array. -/
theorem mixPhi_of_isStage_zero {L : ℕ} (a : LeftStr L → ℤ) {s : MixStr L} (h : IsStage 0 s) :
    mixPhi a s = a (rightPart s) := by
  have hs : ∀ ℓ, s ℓ = .inr (rightPart s ℓ) := by
    intro ℓ
    have hr := (h ℓ).2 (Nat.zero_le _)
    unfold rightPart
    cases hsℓ : s ℓ with
    | inl t => rw [hsℓ] at hr; simp at hr
    | inr v => rfl
  unfold mixPhi
  rw [sum_eq_single (rightPart s)]
  · rw [prod_eq_one (fun ℓ _ => by rw [hs ℓ]; simp [mixCoeff]), mul_one]
  · intro u _ hu
    obtain ⟨ℓ, hℓ⟩ := Function.ne_iff.mp hu
    rw [prod_eq_zero (mem_univ ℓ) (by rw [hs ℓ]; simp [mixCoeff, hℓ]), mul_zero]
  · intro h
    exact absurd (mem_univ _) h

/-- The partial encoding for a string of terms is the encoding `Φ_τ(a)`. -/
theorem mixPhi_inl {L : ℕ} (a : LeftStr L → ℤ) (τ : Leaf L) :
    mixPhi a (Sum.inl ∘ τ) = Phi τ a := rfl

/-- The partial encoding for a string of left variables is the entry of the array. -/
theorem mixPhi_inr {L : ℕ} (a : LeftStr L → ℤ) (u : LeftStr L) :
    mixPhi a (Sum.inr ∘ u) = a u :=
  mixPhi_of_isStage_zero a fun _ => ⟨fun h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩

/-- `A_0[u] = a[u]`. -/
theorem yatesInit_inr {L : ℕ} (a : LeftStr L → ℤ) (u : LeftStr L) :
    yatesInit a (Sum.inr ∘ u) = a u :=
  if_pos fun _ => ⟨fun h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩

/-- The mixed strings of the shape of stage `0` are the strings of left variables. -/
theorem isStage_zero_iff {L : ℕ} (s : MixStr L) : IsStage 0 s ↔ s = Sum.inr ∘ rightPart s := by
  constructor
  · intro h
    funext ℓ
    obtain ⟨v, hv⟩ := Sum.isRight_iff.mp ((h ℓ).2 (Nat.zero_le _))
    simp [rightPart, hv]
  · intro h ℓ
    rw [h]
    exact ⟨fun h' => absurd h' (Nat.not_lt_zero _), fun _ => rfl⟩

/-- `A_0` vanishes at the mixed strings that are not strings of left variables. -/
theorem yatesInit_eq_zero {L : ℕ} (a : LeftStr L → ℤ) {s : MixStr L}
    (h : ∀ u : LeftStr L, s ≠ Sum.inr ∘ u) : yatesInit a s = 0 :=
  if_neg fun h0 => h _ ((isStage_zero_iff s).mp h0)

/-- Replacing the term at level `k` of a string by a left variable turns the shape of stage `k + 1`
into that of stage `k`. -/
theorem isStage_update_iff {L k : ℕ} (hk : k < L) {s : MixStr L} {τ : Term}
    (hs : s ⟨k, hk⟩ = .inl τ) (v : LeftVar) :
    IsStage k (Function.update s ⟨k, hk⟩ (.inr v)) ↔ IsStage (k + 1) s := by
  constructor
  · intro h ℓ
    by_cases hℓ : ℓ = ⟨k, hk⟩
    · subst hℓ
      exact ⟨fun _ => by rw [hs]; rfl, fun h' => by have : k + 1 ≤ k := h'; omega⟩
    · have hne : ℓ.val ≠ k := fun h' => hℓ (Fin.ext h')
      have hℓ' := h ℓ
      rw [Function.update_of_ne hℓ] at hℓ'
      exact ⟨fun h' => hℓ'.1 (by omega), fun h' => hℓ'.2 (by omega)⟩
  · intro h ℓ
    by_cases hℓ : ℓ = ⟨k, hk⟩
    · subst hℓ
      rw [Function.update_self]
      exact ⟨fun h' => by have : k < k := h'; omega, fun _ => rfl⟩
    · have hne : ℓ.val ≠ k := fun h' => hℓ (Fin.ext h')
      rw [Function.update_of_ne hℓ]
      exact ⟨fun h' => (h ℓ).1 (by omega), fun h' => (h ℓ).2 (by omega)⟩

/-- **The arrays of Yates' algorithm.** The array of stage `k` holds the partial encodings at the
strings of the shape of stage `k`, and vanishes at all other mixed strings. -/
theorem yatesStage_eq {L : ℕ} (a : LeftStr L → ℤ) (k : ℕ) (s : MixStr L) :
    yatesStage a k s = if IsStage k s then mixPhi a s else 0 := by
  induction k generalizing s with
  | zero =>
    by_cases h : IsStage 0 s
    · rw [if_pos h, mixPhi_of_isStage_zero a h]
      exact if_pos h
    · rw [if_neg h]
      exact if_neg h
  | succ k ih =>
    rw [yatesStage]
    by_cases hk : k < L
    · rw [dif_pos hk]
      cases hs : s ⟨k, hk⟩ with
      | inl τ =>
        rw [yatesStep_inl _ _ hs]
        simp only [ih, isStage_update_iff hk hs]
        by_cases h : IsStage (k + 1) s
        · simp only [if_pos h]
          exact sum_phi_mul_mixPhi_update a s _ hs
        · simp [if_neg h]
      | inr v =>
        rw [yatesStep_inr _ _ hs, if_neg]
        intro h
        have hl := (h ⟨k, hk⟩).1 (Nat.lt_succ_self k)
        rw [hs] at hl
        simp at hl
    · rw [dif_neg hk, ih]
      have hiff : IsStage k s ↔ IsStage (k + 1) s :=
        ⟨fun h ℓ => ⟨fun _ => (h ℓ).1 (by omega), fun h' => by omega⟩,
          fun h ℓ => ⟨fun _ => (h ℓ).1 (by omega), fun h' => by omega⟩⟩
      simp only [hiff]

/-- **Correctness of Yates' algorithm**: after the steps at all `L` levels, the entry at a leaf
`τ` is the encoding `Φ_τ(a)`. -/
theorem yatesStage_final {L : ℕ} (a : LeftStr L → ℤ) (τ : Leaf L) :
    yatesStage a L (Sum.inl ∘ τ) = Phi τ a := by
  rw [yatesStage_eq, if_pos, mixPhi_inl]
  intro ℓ
  exact ⟨fun _ => rfl, fun h => by omega⟩

/-- The array of stage `k` vanishes outside the strings of the shape of stage `k`. -/
theorem yatesStage_eq_zero_of_not_isStage {L : ℕ} (a : LeftStr L → ℤ) {k : ℕ} {s : MixStr L}
    (h : ¬ IsStage k s) : yatesStage a k s = 0 := by
  rw [yatesStage_eq, if_neg h]

/-- If `a` vanishes off the left strings with exactly `m` inner variables, a partial encoding for
a mixed string with more than `m` inner variables is `0`. -/
theorem mixPhi_eq_zero_of_innerCount {L m : ℕ} {a : LeftStr L → ℤ}
    (ha : ∀ u, (innerSetL u).card ≠ m → a u = 0) {s : MixStr L} (hs : m < innerCount s) :
    mixPhi a s = 0 := by
  unfold mixPhi
  refine sum_eq_zero fun u _ => ?_
  by_cases hu : (innerSetL u).card = m
  · have hex : ∃ ℓ, (∃ v, s ℓ = .inr v ∧ v.IsInner) ∧ ¬ (u ℓ).IsInner := by
      by_contra hcon
      push Not at hcon
      have hsub : (univ.filter fun ℓ => ∃ v, s ℓ = .inr v ∧ v.IsInner) ⊆ innerSetL u := by
        intro ℓ hℓ
        rw [innerSetL, mem_filter]
        exact ⟨mem_univ _, hcon ℓ (mem_filter.mp hℓ).2⟩
      have hle := card_le_card hsub
      unfold innerCount at hs
      omega
    obtain ⟨ℓ, ⟨v, hv, hin⟩, hout⟩ := hex
    have hne : u ℓ ≠ v := fun h => hout (h ▸ hin)
    rw [prod_eq_zero (mem_univ ℓ) (by rw [hv]; simp [mixCoeff, hne]), mul_zero]
  · rw [ha u hu, zero_mul]

/-- **Vanishing**: if `a` vanishes off the left strings with exactly `m` inner variables, an entry
of any stage whose string has more than `m` inner variables is `0`. -/
theorem yatesStage_eq_zero_of_innerCount {L m : ℕ} {a : LeftStr L → ℤ}
    (ha : ∀ u, (innerSetL u).card ≠ m → a u = 0) (k : ℕ) {s : MixStr L}
    (hs : m < innerCount s) : yatesStage a k s = 0 := by
  rw [yatesStage_eq, mixPhi_eq_zero_of_innerCount ha hs, ite_self]

/-- **Locality**: an entry of stage `k + 1` is a combination of the entries of stage `k` at the
strings that have a left variable `v` in place of the term `τ` at level `k`, with the coefficients
`φ_τ(v)`, at most three of which are not `0` (`card_phi_ne_zero_le`). -/
theorem yatesStage_succ {L : ℕ} (a : LeftStr L → ℤ) {k : ℕ} (hk : k < L) {s : MixStr L}
    {τ : Term} (hs : s ⟨k, hk⟩ = .inl τ) :
    yatesStage a (k + 1) s
      = ∑ v, phi τ v * yatesStage a k (Function.update s ⟨k, hk⟩ (.inr v)) := by
  rw [yatesStage, dif_pos hk, yatesStep_inl _ _ hs]

/-- Replacing a symbol of a mixed string by a left variable does not increase the number of
symbols `P₀`. -/
theorem p0Count_update_le {L : ℕ} (s : MixStr L) (ℓ : Fin L) (v : LeftVar) :
    p0Count (Function.update s ℓ (.inr v)) ≤ p0Count s := by
  refine card_le_card fun ℓ' hℓ' => ?_
  rw [mem_filter] at hℓ' ⊢
  refine ⟨mem_univ _, ?_⟩
  by_cases h : ℓ' = ℓ
  · subst h
    simp at hℓ'
  · rw [Function.update_of_ne h] at hℓ'
    exact hℓ'.2

/-- The number of symbols `P₀` of a string of terms. -/
theorem p0Count_inl {L : ℕ} (τ : Leaf L) : p0Count (Sum.inl ∘ τ) = (P0Levels τ).card := by
  unfold p0Count P0Levels
  congr 1
  ext ℓ
  simp

/-- The number of inner variables of a string of left variables. -/
theorem innerCount_inr {L : ℕ} (u : LeftStr L) : innerCount (Sum.inr ∘ u) = (innerSetL u).card := by
  unfold innerCount innerSetL
  congr 1
  ext ℓ
  simp

end ImprovedExponents
