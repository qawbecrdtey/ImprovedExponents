module

public import ImprovedExponents.Optimum.Shapes.Cells_S24
public import ImprovedExponents.Optimum.Shapes.Cells_S34
public import ImprovedExponents.Optimum.Shapes.Cells_S25
public import ImprovedExponents.Optimum.Shapes.Cells_S23
public import ImprovedExponents.Optimum.Shapes.Cells_S26
public import ImprovedExponents.Optimum.Shapes.Cells_S35
public import ImprovedExponents.Optimum.Shapes.Cells_S44
public import ImprovedExponents.Optimum.Shapes.Cells_S45
public import ImprovedExponents.Optimum.Shapes.Cells_S55
public import ImprovedExponents.Optimum.NumValues

@[expose] public section

/-!
# Table 2 of the paper: the saving of the method for the shapes of Schönhage's family

For each shape `(k, n)` of the family other than `(3, 3)`, with `s = kn` outer outputs and inner
length `b = (k - 1)(n - 1)`, the saving `shapeSaving s b c` (see `Shapes/Defs.lean`) is bounded for
every `c > s + 1` by the generated cells of `Shapes/Cells_S{k}{n}*.lean`, and bounded below at
one rational `c₀` near the maximum. The two bounds enclose the supremum `S*` of the saving within
`±10⁻⁶` of its six-digit value:

| shape | `s` | `b` | `c >` | `c₀` | enclosure of `S*` |
|---|---|---|---|---|---|
| `(2, 4)` | `8` | `3` | `9` | `20.1` | `0.001875 < S* ≤ 0.001877` |
| `(3, 4)` | `12` | `6` | `13` | `27.9` | `0.001867 < S* ≤ 0.001869` |
| `(2, 5)` | `10` | `4` | `11` | `24.2` | `0.001776 < S* ≤ 0.001778` |
| `(2, 3)` | `6` | `2` | `7` | `16` | `0.001669 < S* ≤ 0.001671` |
| `(2, 6)` | `12` | `5` | `13` | `28.3` | `0.001623 < S* ≤ 0.001625` |
| `(3, 5)` | `15` | `8` | `16` | `34` | `0.001613 < S* ≤ 0.001615` |
| `(4, 4)` | `16` | `9` | `17` | `35.9` | `0.001573 < S* ≤ 0.001575` |
| `(4, 5)` | `20` | `12` | `21` | `44` | `0.001323 < S* ≤ 0.001325` |
| `(5, 5)` | `25` | `16` | `26` | `54` | `0.001098 < S* ≤ 0.0011` |

For the shape `(3, 3)` the saving is `savingF (basePruned c) (Gam c)` (`shapeSaving_nine_four`),
whose supremum is enclosed in `Optimum/Global.lean`. `shapes_table` collects a coarse upper bound
for every shape together with the lower bound `0.002095 < shapeSaving 9 4 22` of the paper's shape:
no other shape of the family reaches the saving of `(3, 3)`.
-/

namespace ImprovedExponents

open Real Set

/-! ### Assembling the ranges -/

/-- The bound on the whole axis `c > c₀` from the three ranges and the tail of a certificate. -/
theorem shapeSaving_lt_of_ranges {s b : ℕ} {c₀ w₁ w₂ cm u₀ u₁ : ℝ}
    (hbelow : ∀ c ∈ Ioc c₀ w₁, shapeSaving s b c < u₀)
    (hwin : ∀ c ∈ Icc w₁ w₂, shapeSaving s b c < u₁)
    (habove : ∀ c ∈ Icc w₂ cm, shapeSaving s b c < u₀)
    (htail : ∀ c : ℝ, cm ≤ c → shapeSaving s b c < u₀) (hu : u₀ ≤ u₁) {c : ℝ} (hc : c₀ < c) :
    shapeSaving s b c < u₁ := by
  rcases le_total c w₁ with h | h
  · exact (hbelow c ⟨hc, h⟩).trans_le hu
  · rcases le_total c w₂ with h' | h'
    · exact hwin c ⟨h, h'⟩
    · rcases le_total c cm with h'' | h''
      · exact (habove c ⟨h', h''⟩).trans_le hu
      · exact (htail c h'').trans_le hu

/-- The supremum of `shapeSaving s b` over `c > c₀` lies in `(u₀, u₁]` when every value is less
than `u₁` and the value at some `c₁ > c₀` exceeds `u₀`. -/
theorem sSup_shapeSaving_mem {s b : ℕ} {c₀ c₁ u₀ u₁ : ℝ}
    (hlt : ∀ c : ℝ, c₀ < c → shapeSaving s b c < u₁) (hgt : u₀ < shapeSaving s b c₁)
    (hc₁ : c₀ < c₁) : sSup (shapeSaving s b '' Ioi c₀) ∈ Ioc u₀ u₁ := by
  have hne : (shapeSaving s b '' Ioi c₀).Nonempty := ⟨_, c₁, hc₁, rfl⟩
  have hbdd : BddAbove (shapeSaving s b '' Ioi c₀) :=
    ⟨u₁, by rintro _ ⟨c, hc, rfl⟩; exact (hlt c hc).le⟩
  refine ⟨hgt.trans_le (le_csSup hbdd ⟨c₁, hc₁, rfl⟩), csSup_le hne ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  exact (hlt c hc).le

/-! ### The shape `(2, 4)`: `s = 8`, `b = 3` -/

/-- `shapeSaving 8 3 c < 0.001877` for every `c > 9`. -/
theorem shapeSaving_S24_lt (c : ℝ) (hc : 9 < c) : shapeSaving 8 3 c < 0.001877 :=
  shapeSaving_lt_of_ranges shapeSaving_S24_lt_below shapeSaving_S24_lt_window
    shapeSaving_S24_lt_above (fun _ => shapeSaving_S24_lt_tail) (by norm_num) hc

/-- `0.001875 < shapeSaving 8 3 c` at `c = 20.1`. -/
theorem shapeSaving_S24_gt : (0.001875 : ℝ) < shapeSaving 8 3 20.1 :=
  shapeSaving_S24_witness

/-- The supremum of `shapeSaving 8 3` over `c > 9` lies in `(0.001875, 0.001877]`. -/
theorem sSup_shapeSaving_S24_mem :
    sSup (shapeSaving 8 3 '' Ioi 9) ∈ Ioc (0.001875 : ℝ) 0.001877 :=
  sSup_shapeSaving_mem shapeSaving_S24_lt shapeSaving_S24_gt (by norm_num)
/-! ### The shape `(3, 4)`: `s = 12`, `b = 6` -/

/-- `shapeSaving 12 6 c < 0.001869` for every `c > 13`. -/
theorem shapeSaving_S34_lt (c : ℝ) (hc : 13 < c) : shapeSaving 12 6 c < 0.001869 :=
  shapeSaving_lt_of_ranges shapeSaving_S34_lt_below shapeSaving_S34_lt_window
    shapeSaving_S34_lt_above (fun _ => shapeSaving_S34_lt_tail) (by norm_num) hc

/-- `0.001867 < shapeSaving 12 6 c` at `c = 27.9`. -/
theorem shapeSaving_S34_gt : (0.001867 : ℝ) < shapeSaving 12 6 27.9 :=
  shapeSaving_S34_witness

/-- The supremum of `shapeSaving 12 6` over `c > 13` lies in `(0.001867, 0.001869]`. -/
theorem sSup_shapeSaving_S34_mem :
    sSup (shapeSaving 12 6 '' Ioi 13) ∈ Ioc (0.001867 : ℝ) 0.001869 :=
  sSup_shapeSaving_mem shapeSaving_S34_lt shapeSaving_S34_gt (by norm_num)
/-! ### The shape `(2, 5)`: `s = 10`, `b = 4` -/

/-- `shapeSaving 10 4 c < 0.001778` for every `c > 11`. -/
theorem shapeSaving_S25_lt (c : ℝ) (hc : 11 < c) : shapeSaving 10 4 c < 0.001778 :=
  shapeSaving_lt_of_ranges shapeSaving_S25_lt_below shapeSaving_S25_lt_window
    shapeSaving_S25_lt_above (fun _ => shapeSaving_S25_lt_tail) (by norm_num) hc

/-- `0.001776 < shapeSaving 10 4 c` at `c = 24.2`. -/
theorem shapeSaving_S25_gt : (0.001776 : ℝ) < shapeSaving 10 4 24.2 :=
  shapeSaving_S25_witness

/-- The supremum of `shapeSaving 10 4` over `c > 11` lies in `(0.001776, 0.001778]`. -/
theorem sSup_shapeSaving_S25_mem :
    sSup (shapeSaving 10 4 '' Ioi 11) ∈ Ioc (0.001776 : ℝ) 0.001778 :=
  sSup_shapeSaving_mem shapeSaving_S25_lt shapeSaving_S25_gt (by norm_num)
/-! ### The shape `(2, 3)`: `s = 6`, `b = 2` -/

/-- `shapeSaving 6 2 c < 0.001671` for every `c > 7`. -/
theorem shapeSaving_S23_lt (c : ℝ) (hc : 7 < c) : shapeSaving 6 2 c < 0.001671 :=
  shapeSaving_lt_of_ranges shapeSaving_S23_lt_below shapeSaving_S23_lt_window
    shapeSaving_S23_lt_above (fun _ => shapeSaving_S23_lt_tail) (by norm_num) hc

/-- `0.001669 < shapeSaving 6 2 c` at `c = 16`. -/
theorem shapeSaving_S23_gt : (0.001669 : ℝ) < shapeSaving 6 2 16 :=
  shapeSaving_S23_witness

/-- The supremum of `shapeSaving 6 2` over `c > 7` lies in `(0.001669, 0.001671]`. -/
theorem sSup_shapeSaving_S23_mem :
    sSup (shapeSaving 6 2 '' Ioi 7) ∈ Ioc (0.001669 : ℝ) 0.001671 :=
  sSup_shapeSaving_mem shapeSaving_S23_lt shapeSaving_S23_gt (by norm_num)
/-! ### The shape `(2, 6)`: `s = 12`, `b = 5` -/

/-- `shapeSaving 12 5 c < 0.001625` for every `c > 13`. -/
theorem shapeSaving_S26_lt (c : ℝ) (hc : 13 < c) : shapeSaving 12 5 c < 0.001625 :=
  shapeSaving_lt_of_ranges shapeSaving_S26_lt_below shapeSaving_S26_lt_window
    shapeSaving_S26_lt_above (fun _ => shapeSaving_S26_lt_tail) (by norm_num) hc

/-- `0.001623 < shapeSaving 12 5 c` at `c = 28.3`. -/
theorem shapeSaving_S26_gt : (0.001623 : ℝ) < shapeSaving 12 5 28.3 :=
  shapeSaving_S26_witness

/-- The supremum of `shapeSaving 12 5` over `c > 13` lies in `(0.001623, 0.001625]`. -/
theorem sSup_shapeSaving_S26_mem :
    sSup (shapeSaving 12 5 '' Ioi 13) ∈ Ioc (0.001623 : ℝ) 0.001625 :=
  sSup_shapeSaving_mem shapeSaving_S26_lt shapeSaving_S26_gt (by norm_num)
/-! ### The shape `(3, 5)`: `s = 15`, `b = 8` -/

/-- `shapeSaving 15 8 c < 0.001615` for every `c > 16`. -/
theorem shapeSaving_S35_lt (c : ℝ) (hc : 16 < c) : shapeSaving 15 8 c < 0.001615 :=
  shapeSaving_lt_of_ranges shapeSaving_S35_lt_below shapeSaving_S35_lt_window
    shapeSaving_S35_lt_above (fun _ => shapeSaving_S35_lt_tail) (by norm_num) hc

/-- `0.001613 < shapeSaving 15 8 c` at `c = 34`. -/
theorem shapeSaving_S35_gt : (0.001613 : ℝ) < shapeSaving 15 8 34 :=
  shapeSaving_S35_witness

/-- The supremum of `shapeSaving 15 8` over `c > 16` lies in `(0.001613, 0.001615]`. -/
theorem sSup_shapeSaving_S35_mem :
    sSup (shapeSaving 15 8 '' Ioi 16) ∈ Ioc (0.001613 : ℝ) 0.001615 :=
  sSup_shapeSaving_mem shapeSaving_S35_lt shapeSaving_S35_gt (by norm_num)
/-! ### The shape `(4, 4)`: `s = 16`, `b = 9` -/

/-- `shapeSaving 16 9 c < 0.001575` for every `c > 17`. -/
theorem shapeSaving_S44_lt (c : ℝ) (hc : 17 < c) : shapeSaving 16 9 c < 0.001575 :=
  shapeSaving_lt_of_ranges shapeSaving_S44_lt_below shapeSaving_S44_lt_window
    shapeSaving_S44_lt_above (fun _ => shapeSaving_S44_lt_tail) (by norm_num) hc

/-- `0.001573 < shapeSaving 16 9 c` at `c = 35.9`. -/
theorem shapeSaving_S44_gt : (0.001573 : ℝ) < shapeSaving 16 9 35.9 :=
  shapeSaving_S44_witness

/-- The supremum of `shapeSaving 16 9` over `c > 17` lies in `(0.001573, 0.001575]`. -/
theorem sSup_shapeSaving_S44_mem :
    sSup (shapeSaving 16 9 '' Ioi 17) ∈ Ioc (0.001573 : ℝ) 0.001575 :=
  sSup_shapeSaving_mem shapeSaving_S44_lt shapeSaving_S44_gt (by norm_num)
/-! ### The shape `(4, 5)`: `s = 20`, `b = 12` -/

/-- `shapeSaving 20 12 c < 0.001325` for every `c > 21`. -/
theorem shapeSaving_S45_lt (c : ℝ) (hc : 21 < c) : shapeSaving 20 12 c < 0.001325 :=
  shapeSaving_lt_of_ranges shapeSaving_S45_lt_below shapeSaving_S45_lt_window
    shapeSaving_S45_lt_above (fun _ => shapeSaving_S45_lt_tail) (by norm_num) hc

/-- `0.001323 < shapeSaving 20 12 c` at `c = 44`. -/
theorem shapeSaving_S45_gt : (0.001323 : ℝ) < shapeSaving 20 12 44 :=
  shapeSaving_S45_witness

/-- The supremum of `shapeSaving 20 12` over `c > 21` lies in `(0.001323, 0.001325]`. -/
theorem sSup_shapeSaving_S45_mem :
    sSup (shapeSaving 20 12 '' Ioi 21) ∈ Ioc (0.001323 : ℝ) 0.001325 :=
  sSup_shapeSaving_mem shapeSaving_S45_lt shapeSaving_S45_gt (by norm_num)
/-! ### The shape `(5, 5)`: `s = 25`, `b = 16` -/

/-- `shapeSaving 25 16 c < 0.0011` for every `c > 26`. -/
theorem shapeSaving_S55_lt (c : ℝ) (hc : 26 < c) : shapeSaving 25 16 c < 0.0011 :=
  shapeSaving_lt_of_ranges shapeSaving_S55_lt_below shapeSaving_S55_lt_window
    shapeSaving_S55_lt_above (fun _ => shapeSaving_S55_lt_tail) (by norm_num) hc

/-- `0.001098 < shapeSaving 25 16 c` at `c = 54`. -/
theorem shapeSaving_S55_gt : (0.001098 : ℝ) < shapeSaving 25 16 54 :=
  shapeSaving_S55_witness

/-- The supremum of `shapeSaving 25 16` over `c > 26` lies in `(0.001098, 0.0011]`. -/
theorem sSup_shapeSaving_S55_mem :
    sSup (shapeSaving 25 16 '' Ioi 26) ∈ Ioc (0.001098 : ℝ) 0.0011 :=
  sSup_shapeSaving_mem shapeSaving_S55_lt shapeSaving_S55_gt (by norm_num)
/-! ### The table -/

/-- **Table 2**: coarse upper bounds on the saving of the nine other shapes of the family, for all
admissible `c`, and the lower bound `0.002095 < shapeSaving 9 4 22` of the paper's shape `(3, 3)`
(from `savingF_pruned_gt` through the bridge `shapeSaving_nine_four`). -/
theorem shapes_table :
    (∀ c : ℝ, 9 < c → shapeSaving 8 3 c < 0.00188) ∧
    (∀ c : ℝ, 13 < c → shapeSaving 12 6 c < 0.00187) ∧
    (∀ c : ℝ, 11 < c → shapeSaving 10 4 c < 0.00178) ∧
    (∀ c : ℝ, 7 < c → shapeSaving 6 2 c < 0.00168) ∧
    (∀ c : ℝ, 13 < c → shapeSaving 12 5 c < 0.00163) ∧
    (∀ c : ℝ, 16 < c → shapeSaving 15 8 c < 0.00162) ∧
    (∀ c : ℝ, 17 < c → shapeSaving 16 9 c < 0.00158) ∧
    (∀ c : ℝ, 21 < c → shapeSaving 20 12 c < 0.00133) ∧
    (∀ c : ℝ, 26 < c → shapeSaving 25 16 c < 0.0011) ∧
    (0.002095 : ℝ) < shapeSaving 9 4 22 :=
  ⟨fun c hc => (shapeSaving_S24_lt c hc).trans_le (by norm_num),
    fun c hc => (shapeSaving_S34_lt c hc).trans_le (by norm_num),
    fun c hc => (shapeSaving_S25_lt c hc).trans_le (by norm_num),
    fun c hc => (shapeSaving_S23_lt c hc).trans_le (by norm_num),
    fun c hc => (shapeSaving_S26_lt c hc).trans_le (by norm_num),
    fun c hc => (shapeSaving_S35_lt c hc).trans_le (by norm_num),
    fun c hc => (shapeSaving_S44_lt c hc).trans_le (by norm_num),
    fun c hc => (shapeSaving_S45_lt c hc).trans_le (by norm_num),
    fun c hc => (shapeSaving_S55_lt c hc).trans_le (by norm_num),
    (by rw [shapeSaving_nine_four]; exact savingF_pruned_gt)⟩

end ImprovedExponents
