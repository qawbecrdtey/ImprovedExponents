module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Tactic.NormNum.Ineq

@[expose] public section

/-!
# Comparisons as equalities

Let `x, y, u < 2^b` be natural numbers and put
`f(ℓ) := ⌊u/2^ℓ⌋ - ⌊x/2^ℓ⌋ - ⌊y/2^ℓ⌋` (`shiftDiff x y u ℓ`). Then

  `x + y < u  ⟺  f(0) = 1 ∨ ∃ ℓ ≤ b, f(ℓ) = 2 ∨ f(ℓ) = 3`   (`add_lt_iff_shiftDiff`).

So one comparison of a sum with a threshold is a disjunction of `2b + 3` equalities between a
number that depends on `u` only and a sum of a number that depends on `x` only and a number that
depends on `y` only.

Proof: `f(ℓ) = 2 f(ℓ + 1) + e` with `e ∈ {-2, -1, 0, 1}`, the difference of the bits at level `ℓ`
(`shiftDiff_succ_bounds`), and `f(b) = 0`. So `f(ℓ + 1) ≥ 2` forces `f(ℓ) ≥ 2`, down to
`f(0) = u - x - y ≥ 2`. Conversely, if `f(0) ≥ 2`, let `ℓ < b` be the largest level with
`f(ℓ) ≥ 2`; then `f(ℓ + 1) ≤ 1` and `f(ℓ) ≤ 2 f(ℓ + 1) + 1 ≤ 3`.
-/

namespace ImprovedExponents

/-- `f(ℓ) = ⌊u/2^ℓ⌋ - ⌊x/2^ℓ⌋ - ⌊y/2^ℓ⌋`, an integer. -/
def shiftDiff (x y u ℓ : ℕ) : ℤ :=
  ((u / 2 ^ ℓ : ℕ) : ℤ) - ((x / 2 ^ ℓ : ℕ) : ℤ) - ((y / 2 ^ ℓ : ℕ) : ℤ)

/-- `f(0) = u - x - y`. -/
theorem shiftDiff_zero (x y u : ℕ) : shiftDiff x y u 0 = (u : ℤ) - x - y := by
  simp [shiftDiff]

/-- `f(ℓ) = 0` for `ℓ ≥ b`, if `x, y, u < 2^b`. -/
theorem shiftDiff_eq_zero {b x y u ℓ : ℕ} (hx : x < 2 ^ b) (hy : y < 2 ^ b) (hu : u < 2 ^ b)
    (hℓ : b ≤ ℓ) : shiftDiff x y u ℓ = 0 := by
  have hpow : 2 ^ b ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  simp [shiftDiff, Nat.div_eq_of_lt (hx.trans_le hpow), Nat.div_eq_of_lt (hy.trans_le hpow),
    Nat.div_eq_of_lt (hu.trans_le hpow)]

/-- `f(ℓ) = 2 f(ℓ + 1) + e` with `e ∈ {-2, -1, 0, 1}`. -/
theorem shiftDiff_succ_bounds (x y u ℓ : ℕ) :
    2 * shiftDiff x y u (ℓ + 1) - 2 ≤ shiftDiff x y u ℓ
      ∧ shiftDiff x y u ℓ ≤ 2 * shiftDiff x y u (ℓ + 1) + 1 := by
  have h : ∀ n : ℕ, n / 2 ^ (ℓ + 1) = n / 2 ^ ℓ / 2 := fun n => by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  unfold shiftDiff
  rw [h x, h y, h u]
  generalize x / 2 ^ ℓ = X
  generalize y / 2 ^ ℓ = Y
  generalize u / 2 ^ ℓ = U
  omega

/-- If `f(ℓ) ≥ 2` at some level then `f(0) ≥ 2`. -/
theorem two_le_shiftDiff_zero {x y u : ℕ} :
    ∀ ℓ, 2 ≤ shiftDiff x y u ℓ → 2 ≤ shiftDiff x y u 0
  | 0, h => h
  | ℓ + 1, h => two_le_shiftDiff_zero ℓ (by have := (shiftDiff_succ_bounds x y u ℓ).1; omega)

/-- If `f(ℓ) ≥ 2` then `f` takes the value `2` or `3` at a level `≤ b`. -/
theorem exists_shiftDiff_eq {b x y u : ℕ} (hx : x < 2 ^ b) (hy : y < 2 ^ b) (hu : u < 2 ^ b) :
    ∀ d ℓ, ℓ + d = b → 2 ≤ shiftDiff x y u ℓ →
      ∃ ℓ' ≤ b, shiftDiff x y u ℓ' = 2 ∨ shiftDiff x y u ℓ' = 3 := by
  intro d
  induction d with
  | zero =>
    intro ℓ hℓ h2
    rw [shiftDiff_eq_zero hx hy hu (by omega)] at h2
    omega
  | succ d ih =>
    intro ℓ hℓ h2
    by_cases h : 2 ≤ shiftDiff x y u (ℓ + 1)
    · exact ih (ℓ + 1) (by omega) h
    · have := (shiftDiff_succ_bounds x y u ℓ).2
      exact ⟨ℓ, by omega, by omega⟩

/-- **Lemma F (comparisons as equalities).** For natural numbers `x, y, u < 2^b`,
`x + y < u` if and only if `f(0) = 1`, or `f(ℓ) = 2` or `f(ℓ) = 3` for some `ℓ ≤ b`, where
`f(ℓ) = ⌊u/2^ℓ⌋ - ⌊x/2^ℓ⌋ - ⌊y/2^ℓ⌋`. -/
theorem add_lt_iff_shiftDiff {b x y u : ℕ} (hx : x < 2 ^ b) (hy : y < 2 ^ b) (hu : u < 2 ^ b) :
    x + y < u ↔ shiftDiff x y u 0 = 1
      ∨ ∃ ℓ ≤ b, shiftDiff x y u ℓ = 2 ∨ shiftDiff x y u ℓ = 3 := by
  have h0 := shiftDiff_zero x y u
  constructor
  · intro h
    by_cases h1 : shiftDiff x y u 0 = 1
    · exact Or.inl h1
    · exact Or.inr (exists_shiftDiff_eq hx hy hu b 0 (by omega) (by omega))
  · rintro (h1 | ⟨ℓ, -, h2⟩)
    · omega
    · have := two_le_shiftDiff_zero ℓ (by omega : 2 ≤ shiftDiff x y u ℓ)
      omega

end ImprovedExponents
