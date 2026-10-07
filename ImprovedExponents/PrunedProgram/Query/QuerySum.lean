module

public import ThreeSumApsp.Programs.Sec4.Theorem30.QuerySum
public import ImprovedExponents.PrunedProgram.Query.Contracts

@[expose] public section

/-!
# A query, once the digits of its output string are known, on pruned encodings

Upstream's `queryCore_spec` proves the routine `queryCoreBody` (procedure 53: the leaves of order
below `t`, then the boxes) under `QueryCorePre`, which holds the two encodings of the tile as full
segments.  The routine reads an encoding in one place only: a round of the first loop reads the
cell of the leaf τ that it treats (`Query.lowRound`, "sum := sum + aA[code] * aB[code]").  This
leaf contributes to the output string η and has order below `t` (`exists_of_mem_lowList`), so it
has the term `P₀` only at the inner levels of η (`card_P0Levels_le_of_contributes`), of which there
are `m` (`QueryCorePreP.card`): the pruned encodings hold its cell (`SegOn.get`).

`queryCoreP_spec` is `queryCore_spec` under `QueryCorePreP`, with `SegOn` in place of `Seg` for
the two encodings; the program, the time and all the other steps are upstream's.  The parts of the
proof that do not mention the precondition (`Query.lowCount`, `Query.Inv`, `Query.box_term`, …)
are reused; those that do are copied with `QueryCorePreP` in place of `QueryCorePre`, under the
same names with a `P` (`lowRoundP`, `low_specP`, …).

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean` (Apache-2.0).
-/

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

namespace QueryP

open Query

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : QueryCoreArgs} {i : ℕ}

/-! ## The pure side: the terms of the sum -/

/-- The digit 9, which stands at the levels of the subset, occurs m times. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.count_digits)
theorem count_digitsP (C : QueryCorePreP lim μ x) : (digitsO x.η).count 9 = x.m := by
  rw [← card_innerSetO, C.card]

/-- Round i of the first loop treats a leaf τ and adds the product of its two numbers.  The leaf
contributes to the output string, so it has at most m symbols `P₀`: the pruned encodings hold its
cell. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.low_term)
theorem low_termP (C : QueryCorePreP lim μ x) (hi : i < lowCount x) :
    ∃ τ : Leaf x.L, leafAt x i = digitsT τ ∧ (P0Levels τ).card ≤ x.m ∧
      (x.terms.take (i + 1)).sum = (x.terms.take i).sum + x.encA τ * x.encB τ := by
  have hleaf : leafAt x i ∈ lowList x.m x.t (digitsO x.η) :=
    List.mem_map.mpr ⟨_, nineStr_mem hi, rfl⟩
  obtain ⟨τ, hlow, hτ⟩ := exists_of_mem_lowList C.card _ hleaf
  refine ⟨τ, hτ.symm, ?_, ?_⟩
  · -- the leaf contributes to η, which has m inner levels
    simp only [lowLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hlow
    rw [← C.card]
    exact card_P0Levels_le_of_contributes hlow.1
  have hlen : i < (lowList x.m x.t (digitsO x.η)).length := by simpa [lowList] using hi
  have hmember : (lowList x.m x.t (digitsO x.η))[i] = digitsT τ := by
    rw [hτ]
    refine Option.some.inj ((List.getElem?_eq_getElem hlen).symm.trans ?_)
    rw [lowList, List.getElem?_map, List.getElem?_eq_getElem hi, getElem_nineStrs hi]
    rfl
  rw [List.sum_take_succ_getD, QueryCoreArgs.terms, queryTerms,
    List.getD_append _ _ _ _ (by rwa [List.length_map]),
    List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getElem_map, hmember,
    leafProduct_digitsT]

/-! ## The memory and the invariant -/

variable {σ : State}

/-- The digits of the output string are kept. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.segDigits)
theorem segDigitsP (C : QueryCorePreP lim μ x) {μ' : ℕ → ℤ}
    (same : SameOutside2 μ μ' x.ss x.m x.box x.L) :
    SegN μ' x.wd (digitsO x.η) :=
  seg_of_same same C.segDigits (by simpa [length_digits] using C.ss_wd)
    (by simpa [length_digits] using C.box_wd)

/-! ## The two calls that both rounds make -/

section Calls

variable {lo hi : ℕ} {μ₀ : ℕ → ℤ}

/-- scatter(wd, ss, box, L, star) writes the leaf or the box of string number i at box; the string
at ss is kept. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.scatter_meets)
theorem scatter_meetsP (K : Callees lim P) (C : QueryCorePreP lim μ x) (star : Bool)
    (hstr : i < (nineStrs x.m lo hi).length) (hss : SegN μ₀ x.ss (nineStr x.m lo hi i))
    (same : SameOutside2 μ μ₀ x.ss x.m x.box x.L) (hd : d ≤ lim.depth) :
    Meets lim P Proc.scatter d [x.wd, x.ss, x.box, x.L, if star then 1 else 0] μ₀ (tScatter x.L)
      fun _ μ₁ => SegN μ₁ x.box (scatter (digitsO x.η) (starRunIf star (nineStr x.m lo hi i))) ∧
        SegN μ₁ x.ss (nineStr x.m lo hi i) ∧ SameOutside2 μ μ₁ x.ss x.m x.box x.L := by
  obtain ⟨hlen, -⟩ := (mem_nineStrs _).mp (nineStr_mem hstr)
  have hapart := C.ss_box
  refine (K.scatter x.wd x.ss x.box x.L star (digitsO x.η) _ μ₀ (segDigitsP C same) hss
    (length_digits x) (by rw [hlen, count_digitsP C]) C.box_wd
    (by omega) C.wd_lt (by rw [hlen]; exact C.ss_lt) C.box_lt _
      (by omega)).mono le_rfl fun _ μ₁ ⟨hbox, same₁⟩ => ⟨hbox, ?_, same_of_box same same₁⟩
  exact hss.of_sameOutside same₁ (by omega)

/-- nineNext(ss, m, lo, hi) goes on to string number i + 1 and says whether there is one. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.next_meets)
theorem next_meetsP (K : Callees lim P) (C : QueryCorePreP lim μ x)
    (hstr : i < (nineStrs x.m lo hi).length) (hss : SegN μ₀ x.ss (nineStr x.m lo hi i))
    (same : SameOutside2 μ μ₀ x.ss x.m x.box x.L) (hd : d ≤ lim.depth) :
    Meets lim P Proc.nineNext d [x.ss, x.m, lo, hi] μ₀ (tNineNext x.m) fun r μ₁ =>
      r = (if i + 1 < (nineStrs x.m lo hi).length then 1 else 0) ∧
        SegN μ₁ x.ss (nineStr x.m lo hi (i + 1)) ∧ SameOutside2 μ μ₁ x.ss x.m x.box x.L := by
  refine (K.nineNext x.ss x.m lo hi _ μ₀ hss (nineStr_mem hstr) C.ss_lt _ (by omega)).mono le_rfl
    fun r μ₁ ⟨hss₁, hr, same₁⟩ => ⟨?_, nineStr_succ .. ▸ hss₁, same_of_ss same same₁⟩
  rw [hr, isSome_nineNext_nineStr hstr]
  simp

end Calls

/-! ## The two rounds -/

/-- One round of the first loop adds the term of the leaf number i.  The one change to upstream's
proof: the two cells read are those of a leaf with at most m symbols `P₀`, which the pruned
encodings hold (`SegOn.get`). -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.lowRound)
theorem lowRoundP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (hi : i < lowCount x) (h : Inv μ x (x.m - x.t + 1) x.m 0 i σ) :
    Ends lim P d queryLowRound σ (tScatter x.L + tHorner x.L + tNineNext x.m + 31)
      (Inv μ x (x.m - x.t + 1) x.m 0 (i + 1)) := by
  obtain ⟨code, value, μ₀, rfl, hss, same⟩ := h
  light_facts C C.std
  obtain ⟨τ, hτ, hfew, hsum⟩ := low_termP C hi
  -- code := scatter(wd, ss, box, L, 0): the leaf
  light_call (scatter_meetsP K C false hi hss same (by omega)) with _ μ₁ ⟨hbox, hss₁, same₁⟩
  replace hbox : SegN μ₁ x.box (digitsT τ) := hτ ▸ hbox
  -- code := horner(box, L)
  light_call (K.horner x.box x.L (digitsT τ) μ₁ hbox (length_digitsT τ) (digitsT_lt τ)
    C.box_lt C.pow _ (by omega)) with _ μ' ⟨rfl, hμ'⟩
  obtain rfl : μ₁ = μ' := hμ'.symm
  rw [ofDigitList_digitsT]
  -- sum := sum + aA[code] * aB[code]: the leaf has few symbols P₀, so its cells are right
  have hcode : codeT τ < 10 ^ x.L := codeT_lt τ
  light_facts C
  have hreadA : μ₁ (x.aA + codeT τ) = x.encA τ :=
    (segOn_of_same same₁ C.segA C.ss_aA C.box_aA).get hfew
  have hreadB : μ₁ (x.aB + codeT τ) = x.encB τ :=
    (segOn_of_same same₁ C.segB C.ss_aB C.box_aB).get hfew
  have hprod := abs_le.1 (C.prod τ)
  have hfits := abs_le.1 (C.sums (i + 1))
  rw [hsum] at hfits
  light_set ((x.terms.take i).sum + x.encA τ * x.encB τ) using hreadA, hreadB
  -- more := nineNext(ss, m, m - t + 1, m)
  light_call (next_meetsP K C hi hss₁ same₁ (by omega)) with _ μ₂ ⟨rfl, hss₂, same₂⟩
  exact ⟨codeT τ, value, μ₂, by simp [hsum], hss₂, same₂⟩

/-- One round of the second loop adds the value of the box number i. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.boxRound)
theorem boxRoundP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (hi : i < boxCount x) (h : Inv μ x (x.m - x.t) (x.m - x.t) (lowCount x) i σ) :
    Ends lim P d queryBoxRound σ (tScatter x.L + tLookup x.L + tNineNext x.m + 31)
      (Inv μ x (x.m - x.t) (x.m - x.t) (lowCount x) (i + 1)) := by
  obtain ⟨code, value, μ₀, rfl, hss, same⟩ := h
  light_facts C.std
  -- what is known about the box
  obtain ⟨hbox, hsum⟩ := box_term hi
  obtain ⟨π, -, hπ⟩ := exists_of_mem_boxesOf C.t_le C.card _ hbox
  have hlen : (boxAt x i).length = x.L := by rw [boxAt, length_scatter, length_digits]
  -- code := scatter(wd, ss, box, L, 1): the box
  light_call (scatter_meetsP K C true hi hss same (by omega)) with void μ₁ ⟨hbox₁, hss₁, same₁⟩
  -- value := lookup(tr, root, box, L)
  light_call (K.lookup x.tr x.root x.box x.L x.T (boxAt x i) μ₁
    (seg_of_same same₁ C.segT C.ss_tr C.box_tr) hbox₁ hlen (hπ ▸ digitsC_lt π) (C.walk _ hbox)
    C.tr_lt C.box_lt _ (by omega)) with _ μ' ⟨rfl, hμ'⟩
  obtain rfl : μ₁ = μ' := hμ'.symm
  -- sum := sum + value
  have hfits := abs_le.1 (C.sums (lowCount x + (i + 1)))
  rw [hsum] at hfits
  generalize trieLookup x.T x.root (boxAt x i) = val at *
  light_set ((x.terms.take (lowCount x + i)).sum + val)
  -- more := nineNext(ss, m, m - t, m - t)
  light_call (next_meetsP K C hi hss₁ same₁ (by omega)) with _ μ₂ ⟨rfl, hss₂, same₂⟩
  exact ⟨void, val, μ₂, by simp [hsum], hss₂, same₂⟩

/-! ## The two loops -/

/-- Either loop: as long as there is a further string, one round. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.loop)
theorem loopP (C : QueryCorePreP lim μ x) {round : Stmt} {lo hi base b : ℕ}
    (hround : ∀ i σ, i < (nineStrs x.m lo hi).length → Inv μ x lo hi base i σ →
      Ends lim P d round σ (b + 31) (Inv μ x lo hi base (i + 1)))
    (h : Inv μ x lo hi base 0 σ) :
    Ends lim P d (.while (v More =' k 1) round) σ ((nineStrs x.m lo hi).length * (b + 90) + 4)
      (Inv μ x lo hi base (nineStrs x.m lo hi).length) := by
  have hc := C.std.const_le
  have htime := Nat.mul_le_mul_left (nineStrs x.m lo hi).length
    (show 1 + 1 + 1 + 1 + (b + 31) ≤ b + 90 by omega)
  refine Ends.whileConst (Inv μ x lo hi base) (nineStrs x.m lo hi).length (b + 31) h ?round ?done
    (by simp only [Cond.cost, Expr.cost]; omega)
  case round =>
    rintro i σ hi hI
    have hends := hround i σ hi hI
    obtain ⟨code, value, μ', rfl, -⟩ := hI
    exact ⟨by simp; omega, by simp [hi], hends⟩
  case done =>
    rintro σ hI
    have hI' := hI
    obtain ⟨code, value, μ', rfl, -⟩ := hI'
    exact ⟨by simp; omega, by simp, hI⟩

/-- The leaves of order below t. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.low_spec)
theorem low_specP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (ht : 1 ≤ x.t) (h : Mid μ x 0 σ) :
    Ends lim P d queryLow σ
      (tNineFirst x.m + lowCount x * (tScatter x.L + tHorner x.L + tNineNext x.m + 90) + 16)
      (Mid μ x (lowCount x)) := by
  obtain ⟨more, code, value, μ₀, rfl, same⟩ := h
  have htm := C.t_le
  light_facts C C.std
  have hpos : 0 < lowCount x := length_nineStrs_pos (by omega) (by omega)
  -- nineFirst(ss, m, m - t + 1); more := 1
  light_call (K.nineFirst x.ss x.m (x.m - x.t + 1) μ₀ (by omega) C.ss_lt _
    (by omega)) with _ μ₁ ⟨hss, same₁⟩
  light_set 1
  -- the loop
  refine (loopP C (b := tScatter x.L + tHorner x.L + tNineNext x.m)
    (fun i σ hi hI => lowRoundP K C hd hi hI)
    ⟨code, value, μ₁, by simp [hpos], hss, same_of_ss same same₁⟩).mono (by simp [lowCount]; omega)
    fun σ' hI => ?_
  simpa using hI.mid

/-- The boxes. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.boxes_spec)
theorem boxes_specP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (h : Mid μ x (lowCount x) σ) :
    Ends lim P d queryBoxes σ
      (tNineFirst x.m + boxCount x * (tScatter x.L + tLookup x.L + tNineNext x.m + 90) + 16)
      (Mid μ x (lowCount x + boxCount x)) := by
  obtain ⟨more, code, value, μ₀, rfl, same⟩ := h
  light_facts C.std
  have hpos : 0 < boxCount x := length_nineStrs_pos (by omega) le_rfl
  -- nineFirst(ss, m, m - t); more := 1
  light_call (K.nineFirst x.ss x.m (x.m - x.t) μ₀ (by omega) C.ss_lt _ (by omega))
    with _ μ₁ ⟨hss, same₁⟩
  light_set 1
  -- the loop
  exact (loopP C (b := tScatter x.L + tLookup x.L + tNineNext x.m)
    (fun i σ hi hI => boxRoundP K C hd hi hI)
    ⟨code, value, μ₁, by simp [hpos], hss, same_of_ss same same₁⟩).mono (by simp [boxCount]; omega)
    fun σ' hI => hI.mid

/-- The boxes, and the result. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.tail_spec)
theorem tail_specP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (h : Mid μ x (lowCount x) σ) :
    Ends lim P d (queryBoxes ;; .set EncA (v Sum)) σ
      (tNineFirst x.m + boxCount x * (tScatter x.L + tLookup x.L + tNineNext x.m + 90) + 18)
      fun σ' =>
      σ'.loc 0 = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) ∧
        SameOutside2 μ σ'.mem x.ss x.m x.box x.L := by
  -- the boxes
  light_piece (boxes_specP K C hd h) with _ ⟨more, code, value, μ', rfl, same⟩
  have hlen : x.terms.length = lowCount x + boxCount x := by
    simp [QueryCoreArgs.terms, queryTerms, lowList, boxesOf]
  have hall : (x.terms.take (lowCount x + boxCount x)).sum
      = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) := by
    rw [← hlen, List.take_length, QueryCoreArgs.terms, trieQuery]
  rw [hall]
  generalize trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) = result
  -- return sum
  light_set result
  exact ⟨rfl, same⟩

end QueryP

open Query QueryP in
/-- **queryCore** meets its specification on pruned encodings: upstream's routine, under the
assumption that the two encodings are right at the leaves with at most `m` symbols `P₀` only. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (queryCore_spec)
theorem queryCoreP_spec {lim : Limits} {P : Program}
    (hP : P[Proc.queryCore]? = some queryCoreBody) (K : Callees lim P) : QueryCoreSpecP lim P := by
  intro x μ C
  refine fun d hd => ⟨queryCoreBody, hP, ?_⟩
  have htm := C.t_le
  light_facts C C.std
  have hlows : (lowList x.m x.t ([] : List ℕ)).length = lowCount x := by simp [lowList]
  have hboxes : (boxesOf x.m x.t ([] : List ℕ)).length = boxCount x := by simp [boxesOf]
  unfold tQueryCore
  rw [hlows, hboxes]
  -- nines := m - t
  light_set (x.m - x.t : ℕ)
  have hstart : Mid μ x 0 ⟨frame (setLocal [(x.aA : ℤ), x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L,
      x.m, x.t] Nines (x.m - x.t : ℕ)), μ⟩ := ⟨0, 0, 0, μ, by simp, .refl⟩
  -- if t = 0 there are no leaves of order below t
  light_if ht0 ht1 : x.t = 0
  · have hnone : lowCount x = 0 := by
      rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
      intro l hl
      obtain ⟨-, -, hmin, hmax⟩ := (mem_nineStrs l).mp hl
      omega
    light_piece (tail_specP K C hd (hnone ▸ hstart))
  · -- the leaves of order below t, then the boxes
    light_piece (low_specP K C hd (by omega) hstart) with σ' hmid
    light_piece (tail_specP K C hd hmid)

end Light.Sec4
