module

public import ImprovedExponents.Optimum.GlobalCells
public import ImprovedExponents.Optimum.NumValues

@[expose] public section

/-!
# The saving with pruned encodings, for all `c > 10`

For pruned encodings the saving at the parameter `c > 10` is `S(c) = F(A(c), Γ(c))`, that is
`savingF (basePruned c) (Gam c)` (see `Optimum/Defs.lean`). Numerically `S` has one flat maximum
`0.00209531…` at `c ≈ 21.915`. This file bounds `S` on the whole axis:

* `savingF_pruned_lt_global_tight`: `S(c) < 0.002096` for all `c > 10`, and its corollary
  `savingF_pruned_lt_global`: `S(c) < 0.0021`;
* `savingF_pruned_lt_outside`: `S(c) < 0.002095` for `10 < c ≤ 21` and for `c ≥ 23`, hence
  `mem_Ioo_of_savingF_pruned_ge`: every `c > 10` with `S(c) ≥ 0.002095` lies in `(21, 23)`;
* `SstarPruned`, the supremum of `S` over `c > 10`, with `0.002095 < SstarPruned ≤ 0.002096`
  (`SstarPruned_bounds`, `SstarPruned_le`), and `lt_SstarPruned_iff`: a number is less than
  `SstarPruned` if and only if it is less than `S(c)` for some `21 < c < 23`.

## The proof

`A` and `Γ` are nondecreasing, so `S(c) ≤ F(A(c₁), Γ(c₂))` for `c₁ ≤ c ≤ c₂`. The generated files
`GlobalCells1.lean` to `GlobalCells5.lean` cut `(10, 200]` into 222 cells on which this bound,
evaluated with certified rational bounds on `A(c₁)` and `Γ(c₂)`, is below `0.002095` (68 cells
outside `[21, 23]`) or below `0.002096` (154 cells in `[21, 23]`, of width about `0.007` near the
maximum); `GlobalCells.lean` joins them. For `c ≥ 200` the bounds `Γ(c) < 2/3` and
`A(c) ≥ A(200) > 221.77` suffice (`savingF_pruned_lt_tail`). The lower bound on the supremum is
the value at `c = 22` (`savingF_pruned_gt` of `Optimum/NumValues.lean`).

The cells are produced by `python3 -m search.certs` (see `search/certs.py`), which evaluates the
rational inequalities of every cell exactly before it writes them.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

/-! ### The bounds -/

/-- The tail: `F(A(c), Γ(c)) < 0.002095` for `c ≥ 200`, because `Γ(c) < 2/3` and
`A(c) ≥ A(200) = 221.7717…`. -/
theorem savingF_pruned_lt_tail {c : ℝ} (hc : 200 ≤ c) :
    savingF (basePruned c) (Gam c) < 0.002095 :=
  savingF_lt_of_le basePruned_monotoneOn (le_basePruned 8 : (221.77175 : ℝ) ≤ basePruned 200) hc

/-- **Outside the window**: the saving with pruned encodings is less than `0.002095` for
`10 < c ≤ 21` and for `c ≥ 23`. -/
theorem savingF_pruned_lt_outside (c : ℝ) (hc : 10 < c) (hout : c ≤ 21 ∨ 23 ≤ c) :
    savingF (basePruned c) (Gam c) < 0.002095 := by
  rcases hout with h | h
  · exact savingF_pruned_lt_below c ⟨hc, h⟩
  · rcases le_total c 200 with h' | h'
    · exact savingF_pruned_lt_above c ⟨h, h'⟩
    · exact savingF_pruned_lt_tail h'

/-- **The global bound**: the saving with pruned encodings is less than `0.002096` for every
`c > 10` (its supremum is `0.00209531…`). -/
theorem savingF_pruned_lt_global_tight (c : ℝ) (hc : 10 < c) :
    savingF (basePruned c) (Gam c) < 0.002096 := by
  rcases le_total c 21 with h | h
  · exact (savingF_pruned_lt_outside c hc (Or.inl h)).trans (by norm_num)
  · rcases le_total c 23 with h' | h'
    · exact savingF_pruned_lt_window c ⟨h, h'⟩
    · exact (savingF_pruned_lt_outside c hc (Or.inr h')).trans (by norm_num)

/-- The saving with pruned encodings is less than `0.0021` for every `c > 10`. -/
theorem savingF_pruned_lt_global (c : ℝ) (hc : 10 < c) :
    savingF (basePruned c) (Gam c) < 0.0021 :=
  (savingF_pruned_lt_global_tight c hc).trans (by norm_num)

/-- Every `c > 10` at which the saving with pruned encodings is at least `0.002095` lies in
`(21, 23)`. -/
theorem mem_Ioo_of_savingF_pruned_ge (c : ℝ) (hc : 10 < c)
    (h : (0.002095 : ℝ) ≤ savingF (basePruned c) (Gam c)) : c ∈ Set.Ioo (21 : ℝ) 23 := by
  by_contra hmem
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hmem
  exact absurd (savingF_pruned_lt_outside c hc hmem) (not_lt.2 h)

/-! ### The supremum -/

/-- The supremum over `c > 10` of the saving with pruned encodings; it is `0.00209531…`. -/
noncomputable def SstarPruned : ℝ :=
  sSup ((fun c => savingF (basePruned c) (Gam c)) '' Set.Ioi 10)

/-- The savings with pruned encodings are bounded above. -/
theorem bddAbove_savingF_pruned :
    BddAbove ((fun c => savingF (basePruned c) (Gam c)) '' Set.Ioi 10) :=
  ⟨0.002096, by rintro _ ⟨c, hc, rfl⟩; exact (savingF_pruned_lt_global_tight c hc).le⟩

/-- The set of the savings with pruned encodings is not empty. -/
theorem nonempty_savingF_pruned :
    ((fun c => savingF (basePruned c) (Gam c)) '' Set.Ioi 10).Nonempty :=
  ⟨_, 22, by norm_num, rfl⟩

/-- `SstarPruned` is the least upper bound of the savings with pruned encodings. -/
theorem isLUB_SstarPruned :
    IsLUB ((fun c => savingF (basePruned c) (Gam c)) '' Set.Ioi 10) SstarPruned :=
  isLUB_csSup nonempty_savingF_pruned bddAbove_savingF_pruned

/-- Every saving with pruned encodings is at most `SstarPruned`. -/
theorem savingF_pruned_le_SstarPruned {c : ℝ} (hc : 10 < c) :
    savingF (basePruned c) (Gam c) ≤ SstarPruned :=
  le_csSup bddAbove_savingF_pruned ⟨c, hc, rfl⟩

/-- `SstarPruned ≤ 0.002096`. -/
theorem SstarPruned_le : SstarPruned ≤ 0.002096 :=
  csSup_le nonempty_savingF_pruned
    (by rintro _ ⟨c, hc, rfl⟩; exact (savingF_pruned_lt_global_tight c hc).le)

/-- `0.002095 < SstarPruned`, by the value at `c = 22`. -/
theorem lt_SstarPruned : (0.002095 : ℝ) < SstarPruned :=
  savingF_pruned_gt.trans_le (savingF_pruned_le_SstarPruned (by norm_num))

/-- **The supremum of the saving with pruned encodings**: `0.002095 < SstarPruned < 0.0021`
(more precisely `SstarPruned ≤ 0.002096`, see `SstarPruned_le`). -/
theorem SstarPruned_bounds : (0.002095 : ℝ) < SstarPruned ∧ SstarPruned < 0.0021 :=
  ⟨lt_SstarPruned, SstarPruned_le.trans_lt (by norm_num)⟩

/-- Every number less than `SstarPruned` is less than the saving at some `c` in `(21, 23)`. -/
theorem exists_savingF_pruned_gt {s : ℝ} (hs : s < SstarPruned) :
    ∃ c : ℝ, 21 < c ∧ c < 23 ∧ s < savingF (basePruned c) (Gam c) := by
  obtain ⟨_, ⟨c, hc, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup nonempty_savingF_pruned hs
  rcases lt_or_ge s 0.002095 with h | h
  · exact ⟨22, by norm_num, by norm_num, h.trans savingF_pruned_gt⟩
  · have hmem := mem_Ioo_of_savingF_pruned_ge c hc (h.trans hlt.le)
    exact ⟨c, hmem.1, hmem.2, hlt⟩

/-- A number is less than `SstarPruned` if and only if it is less than the saving at some `c` in
`(21, 23)`. -/
theorem lt_SstarPruned_iff {s : ℝ} :
    s < SstarPruned ↔ ∃ c : ℝ, 21 < c ∧ c < 23 ∧ s < savingF (basePruned c) (Gam c) :=
  ⟨exists_savingF_pruned_gt, fun ⟨_, hc, _, h⟩ =>
    h.trans_le (savingF_pruned_le_SstarPruned (lt_trans (by norm_num) hc))⟩

end ImprovedExponents
