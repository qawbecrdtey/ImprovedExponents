module

public import ImprovedExponents.PrunedEncoding.Counts

@[expose] public section

/-!
# Pruned encodings: counting the index strings

`prefCount k m` is the number of strings of `k` terms with at most `m` symbols `P₀`
(`card_termStrings`), and `sufCount n m` is the number of strings of `n` left variables with at most
`m` inner variables (`card_leftStrings`). Both follow from one count: the strings of length `n`
over an alphabet with `c₁` marked and `c₀` unmarked letters that have exactly `j` marked letters
number `C(n, j) c₁^j c₀^{n-j}`. There are `9` terms other than `P₀`, and `4` inner and `3` outer
left variables.
-/

namespace ImprovedExponents

open Finset ThreeSumApsp

/-- The strings of length `n` with exactly `j` letters satisfying `p` number
`C(n, j) c₁^j c₀^{n-j}`, where `c₁` letters satisfy `p` and `c₀` do not. -/
theorem card_filter_card_eq {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (n j : ℕ) :
    (univ.filter fun f : Fin n → α => (univ.filter fun ℓ => p (f ℓ)).card = j).card
      = n.choose j * (univ.filter p).card ^ j * (univ.filter fun a => ¬ p a).card ^ (n - j) := by
  classical
  have hmaps : ∀ f ∈ (univ.filter fun f : Fin n → α => (univ.filter fun ℓ => p (f ℓ)).card = j),
      (univ.filter fun ℓ => p (f ℓ)) ∈ powersetCard j (univ : Finset (Fin n)) := by
    intro f hf
    rw [mem_powersetCard]
    exact ⟨subset_univ _, (mem_filter.mp hf).2⟩
  rw [card_eq_sum_card_fiberwise hmaps]
  have hfiber : ∀ S ∈ powersetCard j (univ : Finset (Fin n)),
      ((univ.filter fun f : Fin n → α => (univ.filter fun ℓ => p (f ℓ)).card = j).filter
        fun f => (univ.filter fun ℓ => p (f ℓ)) = S).card
        = (univ.filter p).card ^ j * (univ.filter fun a => ¬ p a).card ^ (n - j) := by
    intro S hS
    have hSc : S.card = j := (mem_powersetCard.mp hS).2
    have heq : ((univ.filter fun f : Fin n → α => (univ.filter fun ℓ => p (f ℓ)).card = j).filter
        fun f => (univ.filter fun ℓ => p (f ℓ)) = S)
        = Fintype.piFinset fun ℓ =>
            if ℓ ∈ S then univ.filter p else univ.filter fun a => ¬ p a := by
      ext f
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨_, rfl⟩ ℓ
        by_cases h : p (f ℓ) <;> simp [h]
      · intro h
        have hS' : (univ.filter fun ℓ => p (f ℓ)) = S := by
          ext ℓ
          have := h ℓ
          by_cases hℓ : ℓ ∈ S <;> simp_all
        exact ⟨hS' ▸ hSc, hS'⟩
    have h1 : (univ.filter fun ℓ : Fin n => ℓ ∈ S) = S := by ext; simp
    have h2 : (univ.filter fun ℓ : Fin n => ℓ ∉ S) = Sᶜ := by ext; simp
    rw [heq, Fintype.card_piFinset]
    simp only [apply_ite card, prod_ite, prod_const, h1, h2, card_compl, Fintype.card_fin, hSc]
  rw [sum_congr rfl hfiber, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_assoc]

/-- The strings of length `n` with at most `m` letters satisfying `p` number
`∑_{j ≤ m} C(n, j) c₁^j c₀^{n-j}`. -/
theorem card_filter_card_le {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (n m : ℕ) :
    (univ.filter fun f : Fin n → α => (univ.filter fun ℓ => p (f ℓ)).card ≤ m).card
      = ∑ j ∈ range (m + 1),
          n.choose j * (univ.filter p).card ^ j * (univ.filter fun a => ¬ p a).card ^ (n - j) := by
  have hmaps : ∀ f ∈ (univ.filter fun f : Fin n → α => (univ.filter fun ℓ => p (f ℓ)).card ≤ m),
      (univ.filter fun ℓ => p (f ℓ)).card ∈ range (m + 1) := by
    intro f hf
    exact mem_range.mpr (Nat.lt_succ_iff.mpr (mem_filter.mp hf).2)
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun j hj => ?_
  rw [← card_filter_card_eq p n j]
  congr 1
  ext f
  have := Nat.lt_succ_iff.mp (mem_range.mp hj)
  simp only [mem_filter, mem_univ, true_and]
  omega

/-- `P_k`: the strings of `k` terms with at most `m` symbols `P₀`. -/
def termStrings (k m : ℕ) : Finset (Vertex k) := univ.filter fun τ => (P0Levels τ).card ≤ m

/-- `U`: the strings of `n` left variables with at most `m` inner variables. -/
def leftStrings (n m : ℕ) : Finset (LeftStr n) := univ.filter fun u => (innerSetL u).card ≤ m

/-- One of the ten terms is `P₀`. -/
theorem card_term_P0 : (univ.filter fun t : Term => t = Term.P0).card = 1 := by decide

/-- Nine of the ten terms are not `P₀`. -/
theorem card_term_ne_P0 : (univ.filter fun t : Term => ¬ t = Term.P0).card = 9 := by decide

/-- Four of the seven left variables are inner. -/
theorem card_leftVar_inner : (univ.filter fun v : LeftVar => v.IsInner).card = 4 := by decide

/-- Three of the seven left variables are outer. -/
theorem card_leftVar_outer : (univ.filter fun v : LeftVar => ¬ v.IsInner).card = 3 := by decide

/-- `|P_k| = ∑_{j ≤ m} C(k, j) 9^{k-j}`. -/
theorem card_termStrings (k m : ℕ) : (termStrings k m).card = prefCount k m := by
  have h := card_filter_card_le (fun t : Term => t = Term.P0) k m
  rw [card_term_P0, card_term_ne_P0] at h
  unfold termStrings P0Levels prefCount
  convert h using 3
  simp

/-- `|U| = ∑_{i ≤ m} C(n, i) 4^i 3^{n-i}`. -/
theorem card_leftStrings (n m : ℕ) : (leftStrings n m).card = sufCount n m := by
  have h := card_filter_card_le (fun v : LeftVar => v.IsInner) n m
  rw [card_leftVar_inner, card_leftVar_outer] at h
  unfold leftStrings innerSetL sufCount
  convert h using 3

/-- Every left form has at most three nonzero coefficients. -/
theorem card_phi_ne_zero_le (τ : Term) : (univ.filter fun v => phi τ v ≠ 0).card ≤ 3 := by
  revert τ
  decide

end ImprovedExponents
