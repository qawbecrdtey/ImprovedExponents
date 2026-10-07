module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

@[expose] public section

/-!
# Encodings held at the leaves with few symbols `P₀` only

Upstream's programs describe an encoding in the memory by `Seg μ a (arrT enc)`: all `10^L` cells
from `a` hold the values of `enc`.  The pruned encoder (`ImprovedExponents.PrunedProgram.Encode`)
writes only the cells of the leaves with at most `m` symbols `P₀`, which are the only ones the
tile preprocessing and the queries of Theorem 30 read.  `SegOn m μ a enc` says that these cells
are right and nothing about the others.

* `SegOn.of_seg`: a full segment is in particular a partial one.
* `SegOn.congr`, `SegOn.keep`: the predicate depends on the cells of the array only.
* `card_P0Levels_le_of_contributes`: a leaf that contributes to an output string has `P₀` only at
  the inner levels of the string (the queries read such leaves).
-/

namespace Light

open ThreeSumApsp ThreeSumApsp.Spec Finset

variable {L m m' : ℕ} {μ μ' : ℕ → ℤ} {a : ℕ} {enc : Leaf L → ℤ}

/-- The cells from `a` on hold the encoding `enc` at every leaf with at most `m` symbols `P₀`: the
cell `a + codeT τ` holds `enc τ`.  Nothing is said about the other cells. -/
def SegOn (m : ℕ) (μ : ℕ → ℤ) (a : ℕ) (enc : Leaf L → ℤ) : Prop :=
  ∀ τ : Leaf L, (P0Levels τ).card ≤ m → μ (a + codeT τ) = enc τ

/-- Reading the cell of a leaf with at most `m` symbols `P₀`. -/
theorem SegOn.get (h : SegOn m μ a enc) {τ : Leaf L} (hτ : (P0Levels τ).card ≤ m) :
    μ (a + codeT τ) = enc τ := h τ hτ

/-- A full segment holds the encoding at every leaf. -/
theorem SegOn.of_seg (h : Seg μ a (arrT enc)) : SegOn m μ a enc := fun τ _ => by
  rw [h.getD (by rw [length_arrT]; exact codeT_lt τ) 0, getD_arrT]

/-- Fewer leaves. -/
theorem SegOn.mono (hm : m ≤ m') (h : SegOn m' μ a enc) : SegOn m μ a enc :=
  fun τ hτ => h τ (hτ.trans hm)

/-- The predicate only depends on the `10^L` cells of the array. -/
theorem SegOn.congr (h : SegOn m μ a enc) (he : ∀ i < 10 ^ L, μ' (a + i) = μ (a + i)) :
    SegOn m μ' a enc := fun τ hτ => by rw [he _ (codeT_lt τ), h τ hτ]

/-- The predicate is kept if the cells of the array do not change.  By the default proof of `hs`,
the term `h.keep` carries `h` to a later memory across the steps whose promises are in the
context. -/
theorem SegOn.keep (h : SegOn m μ a enc) (hs : SameOn (Inside a (10 ^ L)) μ μ' := by light_keep) :
    SegOn m μ' a enc :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩

/-- Writing outside the array. -/
theorem SegOn.update_out (h : SegOn m μ a enc) {b : ℕ} (hb : b < a ∨ a + 10 ^ L ≤ b) (x : ℤ) :
    SegOn m (Function.update μ b x) a enc :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- A leaf that contributes to an output string has the term `P₀` only at the inner levels of the
string, since only `P_ij` contributes to `z_ij` (`Term.contributes_iff`). -/
theorem P0Levels_subset_innerSetO {η : OutStr L} {τ : Leaf L} (h : τ.Contributes η) :
    P0Levels τ ⊆ innerSetO η := by
  intro ℓ hℓ
  rw [P0Levels, mem_filter] at hℓ
  rw [innerSetO, mem_filter]
  refine ⟨mem_univ _, ?_⟩
  have hc := (Term.contributes_iff _ _).1 (h ℓ)
  rcases hc with hin | hpriv
  · exact hin
  · rw [hℓ.2] at hpriv
    cases hz : η ℓ with
    | z i j => rw [hz] at hpriv; exact absurd hpriv (by simp [OutVar.privateTerm])
    | z0 => trivial

/-- A leaf that contributes to an output string with `m` inner levels has at most `m` symbols
`P₀`. -/
theorem card_P0Levels_le_of_contributes {η : OutStr L} {τ : Leaf L} (h : τ.Contributes η) :
    (P0Levels τ).card ≤ (innerSetO η).card :=
  card_le_card (P0Levels_subset_innerSetO h)

end Light
