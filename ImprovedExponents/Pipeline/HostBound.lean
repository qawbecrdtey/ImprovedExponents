module

public import ThreeSumApsp.TimeClaims.Sec3.Theorem19
public import ImprovedExponents.Pipeline.ThinClaim

@[expose] public section

/-!
# From the thin product to Exact Triangle: the statements

The deduction of Section 3 of the paper, for arbitrary parameters. The three statements are about a
time model `M : DetTimeModel`, as upstream's `Claim.Corollary_16`, `Claim.Theorem_17` and
`Claim.Theorem_19_explicit`, whose parameters they generalize.

* `LopClaim M ε γ q`: Lop-AE-SparseTri(n, D) with `w` query pairs is solved, for `D ≤ n^ε`, in time
  `O(n² (log D + 1)²/D^γ + w D^q (log D + 1))`. (Corollary 16 has `γ = 0.063`, `q = 0.437` and
  `ε = 1/18`.)
* `HostBound M MM D g Dc`: the bound of Theorem 17 for the parameters `D(n)` and `g(n)`, with every
  call of the solver charged at the dimension `Dc(n)` of the middle part. For `Dc = D` this is
  `Claim.Theorem_17` (`hostBound_iff_theorem_17`).
* `ExplicitFrom M δ e`: Exact Triangle in time `K κ n^{3-δ} (log n)^e` for weights up to `n^κ`, from
  some size `n₀` on. (`Claim.Theorem_19_explicit` has `n₀ = 16^18`.)
-/

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4

/-- Lop-AE-SparseTri (detection) is solved by one procedure whose time on the instances with
`D ≤ n^ε` is at most a constant times `n² (log D + 1)²/D^γ + w D^q (log D + 1)`. -/
def LopClaim (M : DetTimeModel) (ε γ q : ℝ) : Prop :=
  ∃ (C : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), M.lopDetect Td ∧
    ∀ n D w : ℕ, 1 ≤ n → 1 ≤ D → (D : ℝ) ≤ (n : ℝ) ^ ε →
      Td n D w ≤ C * (preBound31 γ n D + (w : ℝ) * queryBound31 q D)

/-- The bound of Theorem 17 for the parameters `D(n)` and `g(n)`, with each of the at most `4ng`
calls of the solver charged at the dimension `Dc(n)`. -/
def HostBound (M : DetTimeModel) (MM : ℕ → ℝ) (D g Dc : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ → ℕ → ℕ → ℝ, M.lopDetect T →
    ∃ T' : ℕ → ℝ → ℝ, M.exactTriangle T' ∧
      ∀ (n : ℕ) (κ u : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
        u ≤ (n : ℝ) ^ κ →
        T' n u ≤ 4 * (n : ℝ) * (g n : ℝ) *
            (T n (Dc n) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
          C * (termScans n (g n) κ + termPrime MM n (D n) + termBuild n (D n) (g n))

/-- With the solver charged at `D(n)` itself, `HostBound` is upstream's `Claim.Theorem_17`. -/
theorem hostBound_iff_theorem_17 (M : DetTimeModel) (MM : ℕ → ℝ) (D g : ℕ → ℕ) :
    HostBound M MM D g D ↔ Claim.Theorem_17 M MM D g :=
  Iff.rfl

/-- Exact Triangle is solved by one algorithm that, from some size `n₀` on and for every `κ ≥ 1`,
takes time at most `K κ n^{3-δ} (log n)^e` on weights of absolute value at most `n^κ`. -/
def ExplicitFrom (M : DetTimeModel) (δ : ℝ) (e : ℕ) : Prop :=
  ∃ (n₀ : ℕ) (K : ℝ) (T : ℕ → ℝ → ℝ), M.exactTriangle T ∧
    ∀ (n : ℕ) (κ u : ℝ), n₀ ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))

/-- `Claim.Theorem_19_explicit` is `ExplicitFrom` with `n₀ = 16^18`. -/
theorem ExplicitFrom.of_theorem_19_explicit {M : DetTimeModel} {δ : ℝ} {e : ℕ}
    (h : Claim.Theorem_19_explicit M δ e) : ExplicitFrom M δ e := by
  obtain ⟨K, T, hT, hb⟩ := h
  exact ⟨16 ^ 18, K, T, hT, hb⟩

end ImprovedExponents
