module

public import ImprovedExponents.Optimum.GlobalFullCells
public import ImprovedExponents.Optimum.NumValues

@[expose] public section

/-!
# The saving with the paper's encodings, for all `c > 10`

For the paper's encodings the saving at the parameter `c > 10` is `S(c) = F(A(c), Γ(c))`, that is
`savingF (baseFull c) (Gam c)` (see `Optimum/Defs.lean`). Numerically `S` has one flat maximum
`0.00205991…` at `c ≈ 21.38`. This file bounds `S` on the whole axis:

* `savingF_full_lt_global_tight`: `S(c) < 0.002061` for all `c > 10`, and its corollary
  `savingF_full_lt_global`: `S(c) < 0.0021`;
* `savingF_full_lt_outside`: `S(c) < 0.002059` for `10 < c ≤ 20.8` and for `c ≥ 22`, hence
  `mem_Ioo_of_savingF_full_ge`: every `c > 10` with `S(c) ≥ 0.002059` lies in `(20.8, 22)`;
* `SstarFull`, the supremum of `S` over `c > 10`, with `0.002059 < SstarFull ≤ 0.002061`
  (`SstarFull_bounds`, `SstarFull_le`), and `lt_SstarFull_iff`: a number is less than
  `SstarFull` if and only if it is less than `S(c)` for some `20.8 < c < 22`.

## The proof

`A` and `Γ` are nondecreasing, so `S(c) ≤ F(A(c₁), Γ(c₂))` for `c₁ ≤ c ≤ c₂`. The generated files
`GlobalFullCells1.lean` to `GlobalFullCells6.lean` cut `(10, 200]` into 261 cells on which this
bound, evaluated with certified rational bounds on `A(c₁)` and `Γ(c₂)`, is below `0.002059`
(173 cells outside `[20.8, 22]`, narrow near the ends of the window, where `S` is close to
`0.002059`) or below `0.002061` (88 cells in `[20.8, 22]`, of width about `0.011` near the
maximum); `GlobalFullCells.lean` joins them. For `c ≥ 200` the bounds
`Γ(c) < 2/3` and `A(c) ≥ A(200) > 238.74` suffice (`savingF_full_lt_tail`). The lower bound on
the supremum is the value at `c = 107/5` (`savingF_full_107_5_gt` of `Optimum/NumValues.lean`).

The cells are produced by `python3 -m search.certs --encoding full` (see `search/certs.py`),
which evaluates the rational inequalities of every cell exactly before it writes them.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

/-! ### The bounds -/

/-- The tail: `F(A(c), Γ(c)) < 0.002059` for `c ≥ 200`, because `Γ(c) < 2/3` and
`A(c) ≥ A(200) = 238.7452…`. -/
theorem savingF_full_lt_tail {c : ℝ} (hc : 200 ≤ c) :
    savingF (baseFull c) (Gam c) < 0.002059 :=
  savingF_lt_of_le baseFull_monotoneOn (le_baseFull 8 : (238.74526 : ℝ) ≤ baseFull 200) hc

/-- **Outside the window**: the saving with the paper's encodings is less than `0.002059` for
`10 < c ≤ 20.8` and for `c ≥ 22`. -/
theorem savingF_full_lt_outside (c : ℝ) (hc : 10 < c) (hout : c ≤ 20.8 ∨ 22 ≤ c) :
    savingF (baseFull c) (Gam c) < 0.002059 := by
  rcases hout with h | h
  · exact savingF_full_lt_below c ⟨hc, h⟩
  · rcases le_total c 200 with h' | h'
    · exact savingF_full_lt_above c ⟨h, h'⟩
    · exact savingF_full_lt_tail h'

/-- **The global bound**: the saving with the paper's encodings is less than `0.002061` for every
`c > 10` (its supremum is `0.00205991…`). -/
theorem savingF_full_lt_global_tight (c : ℝ) (hc : 10 < c) :
    savingF (baseFull c) (Gam c) < 0.002061 := by
  rcases le_total c 20.8 with h | h
  · exact (savingF_full_lt_outside c hc (Or.inl h)).trans (by norm_num)
  · rcases le_total c 22 with h' | h'
    · exact savingF_full_lt_window c ⟨h, h'⟩
    · exact (savingF_full_lt_outside c hc (Or.inr h')).trans (by norm_num)

/-- The saving with the paper's encodings is less than `0.0021` for every `c > 10`. -/
theorem savingF_full_lt_global (c : ℝ) (hc : 10 < c) :
    savingF (baseFull c) (Gam c) < 0.0021 :=
  (savingF_full_lt_global_tight c hc).trans (by norm_num)

/-- Every `c > 10` at which the saving with the paper's encodings is at least `0.002059` lies in
`(20.8, 22)`. -/
theorem mem_Ioo_of_savingF_full_ge (c : ℝ) (hc : 10 < c)
    (h : (0.002059 : ℝ) ≤ savingF (baseFull c) (Gam c)) : c ∈ Set.Ioo (20.8 : ℝ) 22 := by
  by_contra hmem
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hmem
  exact absurd (savingF_full_lt_outside c hc hmem) (not_lt.2 h)

/-! ### The supremum -/

/-- The supremum over `c > 10` of the saving with the paper's encodings; it is `0.00205991…`. -/
noncomputable def SstarFull : ℝ :=
  sSup ((fun c => savingF (baseFull c) (Gam c)) '' Set.Ioi 10)

/-- The savings with the paper's encodings are bounded above. -/
theorem bddAbove_savingF_full :
    BddAbove ((fun c => savingF (baseFull c) (Gam c)) '' Set.Ioi 10) :=
  ⟨0.002061, by rintro _ ⟨c, hc, rfl⟩; exact (savingF_full_lt_global_tight c hc).le⟩

/-- The set of the savings with the paper's encodings is not empty. -/
theorem nonempty_savingF_full :
    ((fun c => savingF (baseFull c) (Gam c)) '' Set.Ioi 10).Nonempty :=
  ⟨_, 107 / 5, by norm_num, rfl⟩

/-- `SstarFull` is the least upper bound of the savings with the paper's encodings. -/
theorem isLUB_SstarFull :
    IsLUB ((fun c => savingF (baseFull c) (Gam c)) '' Set.Ioi 10) SstarFull :=
  isLUB_csSup nonempty_savingF_full bddAbove_savingF_full

/-- Every saving with the paper's encodings is at most `SstarFull`. -/
theorem savingF_full_le_SstarFull {c : ℝ} (hc : 10 < c) :
    savingF (baseFull c) (Gam c) ≤ SstarFull :=
  le_csSup bddAbove_savingF_full ⟨c, hc, rfl⟩

/-- `SstarFull ≤ 0.002061`. -/
theorem SstarFull_le : SstarFull ≤ 0.002061 :=
  csSup_le nonempty_savingF_full
    (by rintro _ ⟨c, hc, rfl⟩; exact (savingF_full_lt_global_tight c hc).le)

/-- `0.002059 < SstarFull`, by the value at `c = 107/5`. -/
theorem lt_SstarFull : (0.002059 : ℝ) < SstarFull :=
  savingF_full_107_5_gt.trans_le (savingF_full_le_SstarFull (by norm_num))

/-- **The supremum of the saving with the paper's encodings**: `0.002059 < SstarFull < 0.0021`
(more precisely `SstarFull ≤ 0.002061`, see `SstarFull_le`). -/
theorem SstarFull_bounds : (0.002059 : ℝ) < SstarFull ∧ SstarFull < 0.0021 :=
  ⟨lt_SstarFull, SstarFull_le.trans_lt (by norm_num)⟩

/-- Every number less than `SstarFull` is less than the saving at some `c` in `(20.8, 22)`. -/
theorem exists_savingF_full_gt {s : ℝ} (hs : s < SstarFull) :
    ∃ c : ℝ, 20.8 < c ∧ c < 22 ∧ s < savingF (baseFull c) (Gam c) := by
  obtain ⟨_, ⟨c, hc, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup nonempty_savingF_full hs
  rcases lt_or_ge s 0.002059 with h | h
  · exact ⟨107 / 5, by norm_num, by norm_num, h.trans savingF_full_107_5_gt⟩
  · have hmem := mem_Ioo_of_savingF_full_ge c hc (h.trans hlt.le)
    exact ⟨c, hmem.1, hmem.2, hlt⟩

/-- A number is less than `SstarFull` if and only if it is less than the saving at some `c` in
`(20.8, 22)`. -/
theorem lt_SstarFull_iff {s : ℝ} :
    s < SstarFull ↔ ∃ c : ℝ, 20.8 < c ∧ c < 22 ∧ s < savingF (baseFull c) (Gam c) :=
  ⟨exists_savingF_full_gt, fun ⟨_, hc, _, h⟩ =>
    h.trans_le (savingF_full_le_SstarFull (lt_trans (by norm_num) hc))⟩

end ImprovedExponents
