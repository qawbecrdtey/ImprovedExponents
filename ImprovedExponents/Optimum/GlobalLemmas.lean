module

public import ImprovedExponents.Optimum.NumLog

@[expose] public section

/-!
# Lemmas for the subdivision of the axis `c > 10`

The saving `F(A(c), Γ(c))` is bounded for all `c > 10` by cutting `(10, ∞)` into cells. On a cell
`[c₁, c₂]` the constant `A` is at least `A(c₁)` and the exponent `Γ` is at most `Γ(c₂)`, so that
`F(A(c), Γ(c)) ≤ F(A(c₁), Γ(c₂))` (`savingF_lt_of_mem_Icc` of `Optimum/NumLog.lean`). This file has
the two other kinds of cells and the lemma that joins adjacent cells:

* `savingF_lt_of_mem_Ioc`: the first cell `(10, c₂]`, with `A(10)` as the lower bound on `A`;
* `savingF_lt_of_le`: the tail `[c₀, ∞)`, with `Γ(c) < 2/3`;
* `forall_mem_Icc_of_forall_mem_Icc`, `forall_mem_Ioc_of_forall_mem_Icc`: a statement that holds
  on `[a, b]` (or `(a, b]`) and on `[b, d]` holds on `[a, d]` (or `(a, d]`).
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

/-- The first cell of a grid in `c`: if `base` is nondecreasing on `[10, ∞)`, then
`F(base c, Γ(c)) < s` for all `10 < c ≤ c₂`, from `Alo ≤ base 10` and `Γ(c₂) ≤ γhi`. -/
theorem savingF_lt_of_mem_Ioc {base : ℝ → ℝ} (hbase : MonotoneOn base (Ici 10))
    {c₂ c Alo γhi s : ℝ} (hA : Alo ≤ base 10) (hγ : Gam c₂ ≤ γhi) (hc : c ∈ Ioc 10 c₂)
    (hAlo : 0 < Alo := by numlog) (hs0 : 0 ≤ s := by numlog) (hs : s ≤ 1 / 2 := by numlog)
    (h : γhi * (1 - 2 * s) * (2 * logTwoHi) < 2 * s * Alo := by numlog) :
    savingF (base c) (Gam c) < s :=
  savingF_lt (hA.trans (hbase (mem_Ici.2 le_rfl) (mem_Ici.2 hc.1.le) hc.1.le)) (Gam_pos hc.1).le
    ((Gam_monotoneOn hc.1 (hc.1.trans_le hc.2) hc.2).trans hγ) hAlo hs0 hs h

/-- The tail of a grid in `c`: if `base` is nondecreasing on `[10, ∞)`, then
`F(base c, Γ(c)) < s` for all `c ≥ c₀`, from `Alo ≤ base c₀` and `Γ(c) < 2/3`. -/
theorem savingF_lt_of_le {base : ℝ → ℝ} (hbase : MonotoneOn base (Ici 10))
    {c₀ c Alo s : ℝ} (hA : Alo ≤ base c₀) (hc : c₀ ≤ c) (hc₀ : 10 < c₀ := by numlog)
    (hAlo : 0 < Alo := by numlog) (hs0 : 0 ≤ s := by numlog) (hs : s ≤ 1 / 2 := by numlog)
    (h : 2 / 3 * (1 - 2 * s) * (2 * logTwoHi) < 2 * s * Alo := by numlog) :
    savingF (base c) (Gam c) < s :=
  have hc10 : 10 < c := hc₀.trans_le hc
  savingF_lt (hA.trans (hbase hc₀.le hc10.le hc)) (Gam_pos hc10).le (Gam_lt_two_thirds hc10).le
    hAlo hs0 hs h

/-- A statement that holds on `[a, b]` and on `[b, d]` holds on `[a, d]`. -/
theorem forall_mem_Icc_of_forall_mem_Icc {P : ℝ → Prop} {a b d : ℝ} (h₁ : ∀ c ∈ Icc a b, P c)
    (h₂ : ∀ c ∈ Icc b d, P c) : ∀ c ∈ Icc a d, P c := fun c hc =>
  (le_total c b).elim (fun h => h₁ c ⟨hc.1, h⟩) fun h => h₂ c ⟨h, hc.2⟩

/-- A statement that holds on `(a, b]` and on `[b, d]` holds on `(a, d]`. -/
theorem forall_mem_Ioc_of_forall_mem_Icc {P : ℝ → Prop} {a b d : ℝ} (h₁ : ∀ c ∈ Ioc a b, P c)
    (h₂ : ∀ c ∈ Icc b d, P c) : ∀ c ∈ Ioc a d, P c := fun c hc =>
  (le_total c b).elim (fun h => h₁ c ⟨hc.1, h⟩) fun h => h₂ c ⟨h, hc.2⟩

end ImprovedExponents
