module

public import ImprovedExponents.ExactCount.Tail

@[expose] public section

/-!
# The parameters of the method and its saving: definitions

The method has four real parameters.

* `c > 10`: the recursion has `L = ⌈cm⌉` levels, `m` of them inner (`D = 4^m`).
* `0 < θ < 0.9`: leaves of order at least `θm` are precomputed as boxes; a query reads the others.
* `1/2 ≤ σ < 1`: the reduction from Exact Triangle hashes modulo a prime `p ≈ D^σ`, so an instance
  has at most `n²/D^σ` query pairs.
* `ε > 0`: the inner dimension is `D ≈ n^ε`.

A thin product then costs `N² (D^{-γX(c,θ)} + D^{q(θ) - σ})` up to factors `log D`, provided that
`ε < R(γX(c, θ))`, where `R(γ) = ln 4/(A + γ ln 4)` is the thinness bound: `A = ln Λ` at `γ = 0` for
the paper's encodings (`baseFull`, so that `R = R_c` of the paper's equation (11)), and
`A = (c/2) H(1/c) + (c - 1) ln 3` for pruned encodings (`basePruned`). Exact Triangle is solved in
time `n^{3 - s}` for every `s` below `tupleSaving c θ σ ε = ε min(2σ - 1, γ - (2σ - 1))` with
`γ = min(γX(c, θ), σ - q(θ))`.

For a fixed `c`, the least upper bound of these savings is `savingF A (Gam c) = R(Γ) Γ/2`, where
`Γ(c) = sup_θ min(γX(c, θ), γ_Q(θ))` and `γ_Q(θ) = (2 - 4 q(θ))/3`. This file has the definitions
only.
-/

namespace ImprovedExponents

open ThreeSumApsp

/-- `γ_Q(θ) := (2 - 4 q(θ))/3`: the largest `γ` with `γ ≤ σ - q(θ)` at the balanced prime size
`σ = 1/2 + γ/4`. -/
noncomputable def gammaQ (θ : ℝ) : ℝ := (2 - 4 * qOf θ) / 3

/-- `Γ(c) := sup_{0 < θ < 0.9} min(γX(c, θ), γ_Q(θ))`, the best exponent of a thin product. -/
noncomputable def Gam (c : ℝ) : ℝ :=
  sSup ((fun θ => min (gammaX c θ) (gammaQ θ)) '' Set.Ioo 0 (9 / 10))

/-- The thinness bound `R(γ) = ln 4/(A + γ ln 4)`: a thin product needs `D ≤ N^ε` with
`ε < R(γ)`. -/
noncomputable def thinR (A γ : ℝ) : ℝ := Real.log 4 / (A + γ * Real.log 4)

/-- The constant `A` of the thinness bound with the paper's encodings (all `10^L` leaves):
`ln Λ` at `γ = 0`, so that `thinR (baseFull c) γ = R_c(γ)`. -/
noncomputable def baseFull (c : ℝ) : ℝ := lnΛ c 0

/-- The constant `A` of the thinness bound with pruned encodings (leaves with at most `m` symbols
`P₀`): `(c/2) H(1/c) + (c - 1) ln 3`, the exponential rate of `√K N₀`. -/
noncomputable def basePruned (c : ℝ) : ℝ := c / 2 * entropy (1 / c) + (c - 1) * Real.log 3

/-- The thinness bound with pruned encodings, `R'_c(γ)`. -/
noncomputable def RcP (c γ : ℝ) : ℝ := thinR (basePruned c) γ

/-- The saving at the exponent `γ` when everything is balanced: `R(γ) γ/2`. -/
noncomputable def savingF (A γ : ℝ) : ℝ := thinR A γ * γ / 2

/-- The exponent of a thin product at inner dimension `D` with at most `N²/D^σ` wanted entries:
`min(γX(c, θ), σ - q(θ))`. -/
noncomputable def effGamma (c θ σ : ℝ) : ℝ := min (gammaX c θ) (σ - qOf θ)

/-- The saving of Exact Triangle at the parameters `(c, θ, σ, ε)`:
`ε min(2σ - 1, γ - (2σ - 1))`. -/
noncomputable def tupleSaving (c θ σ ε : ℝ) : ℝ :=
  ε * min (2 * σ - 1) (effGamma c θ σ - (2 * σ - 1))

/-- The parameters that the method allows, for the thinness constant `A`. -/
structure AdmissibleX (A c θ σ ε : ℝ) : Prop where
  c_gt : 10 < c
  θ_pos : 0 < θ
  θ_lt : θ < 9 / 10
  σ_ge : 1 / 2 ≤ σ
  σ_lt : σ < 1
  ε_pos : 0 < ε
  thin : ε < thinR A (gammaX c θ)

/-- `R_c(γ)` of the paper is the thinness bound with the constant `baseFull c`. -/
theorem Rc_eq_thinR (c γ : ℝ) : Rc c γ = thinR (baseFull c) γ := by
  rw [Rc, thinR, baseFull, lnΛ_eq_add]

end ImprovedExponents
