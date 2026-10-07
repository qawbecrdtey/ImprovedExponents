module

public import ImprovedExponents.AllEdges.Host.Flags

@[expose] public section

/-!
# Reading the answers of one instance and scanning for witnesses, with flags

Footnote 10 of the paper: the proof of Theorem 17 "also solves the all-edges version of Exact
Triangle (scanning each pair only until its zero triangle is found)".

scanPairsAE(out, qa, qb, w, flg, ab, bc, ac, n, c0, len) is upstream's scanPairs with the flag `f`
replaced by the base address `flg` of the `n²` flags: for every query pair number `i < w` whose
answer `out[i]` is not 0, if the flag of the pair `(qa[i], qb[i])`, the cell `flg + qa[i] n +
qb[i]`, is 0, scan the piece `{c0, …, c0 + len - 1}` for a zero triangle through the pair and store
the result in the flag (`scanPairsAE_spec`).  The pure side is `aeStep` and `aeExecs` of
`Flags.lean`.
-/

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace ScanPairsAE

/-- The locals of `scanPairsAE`.  The arguments: the addresses of the answers and of the rows and
the columns of the query pairs, their number `w`, the address of the flags, the addresses of the
three arrays of weights, `n`, and the first vertex and the number of vertices of the piece.  Then
the counter, the address of the flag of the current pair, and the result of its scan. -/
abbrev Out : ℕ := 0
@[inherit_doc Out] abbrev Rows : ℕ := 1
@[inherit_doc Out] abbrev Cols : ℕ := 2
@[inherit_doc Out] abbrev Num : ℕ := 3
@[inherit_doc Out] abbrev Flg : ℕ := 4
@[inherit_doc Out] abbrev AdrAB : ℕ := 5
@[inherit_doc Out] abbrev AdrBC : ℕ := 6
@[inherit_doc Out] abbrev AdrAC : ℕ := 7
@[inherit_doc Out] abbrev Size : ℕ := 8
@[inherit_doc Out] abbrev First : ℕ := 9
@[inherit_doc Out] abbrev Len : ℕ := 10
@[inherit_doc Out] abbrev Cnt : ℕ := 11
@[inherit_doc Out] abbrev Idx : ℕ := 12
@[inherit_doc Out] abbrev Res : ℕ := 13

end ScanPairsAE

open ScanPairsAE in
/-- One query pair: if out[i] ≠ 0 then idx := flg + qa[i] n + qb[i]; if M idx = 0 then
M idx := scan(ab, bc, ac, n, qa[i], qb[i], c0, len). -/
def scanPairsAEStep (pScan : ℕ) : Stmt :=
  .ite (M (v Out +' v Cnt) =' k 0) .skip
    (.set Idx (v Flg +' M (v Rows +' v Cnt) *' v Size +' M (v Cols +' v Cnt)) ;;
      .ite (M (v Idx) =' k 0)
        (.call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, M (v Rows +' v Cnt),
          M (v Cols +' v Cnt), v First, v Len] Res ;;
          .store (v Idx) (v Res))
        .skip)

open ScanPairsAE in
/-- scanPairsAE(out, qa, qb, w, flg, ab, bc, ac, n, c0, len); the parameter is the procedure number
of `scan`. -/
def scanPairsAEBody (pScan : ℕ) : Stmt :=
  .set Cnt (k 0) ;;
  .while (v Cnt <' v Num) (scanPairsAEStep pScan ;; .set Cnt (v Cnt +' k 1))

/-- The time for reading w answers and the flags of the accepted pairs. -/
def tAnswersAE (w : ℕ) : ℕ := 68 * w + 6

/-- The time of one scan of a piece of len vertices, with its call and the store of its result. -/
def tScanCallAE (len : ℕ) : ℕ := tScan len + 30

/-- The time of scanPairsAE, given the number of scans. -/
def tScanPairsAE (w len execs : ℕ) : ℕ := tAnswersAE w + tScanCallAE len * execs

/-- The cell `a n + b` of the query pair number `i`, in the lists of its rows and columns. -/
def idxOf (n : ℕ) (QA QB : List ℕ) (i : ℕ) : ℕ := QA.getD i 0 * n + QB.getD i 0

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {out qa qb w ab bc ac n c0 len U flg : ℕ}
  {OUT AB BC AC F : List ℤ} {QA QB : List ℕ}

/-- What `scanPairsAE` assumes about the flags: `n²` cells at `flg`, within the memory and apart
from the three arrays of weights. -/
structure FlagsAt (lim : Limits) (μ : ℕ → ℤ) (flg ab bc ac n : ℕ) (F : List ℤ) : Prop where
  len : F.length = n * n
  seg : Seg μ flg F
  below : flg + n * n ≤ lim.space
  apartAB : Apart flg (n * n) ab (n * n)
  apartBC : Apart flg (n * n) bc (n * n)
  apartAC : Apart flg (n * n) ac (n * n)

/-- The state of `scanPairsAE` when `i` query pairs have been treated and the counter is `j`. -/
def scanPairsAEState (μ : ℕ → ℤ) (out qa qb w flg ab bc ac n c0 len : ℕ) (OUT AB BC AC F : List ℤ)
    (QA QB : List ℕ) (i j : ℕ) (idx res : ℤ) : State :=
  ⟨frame [out, qa, qb, w, flg, ab, bc, ac, n, c0, len, j, idx, res],
    wrote μ flg
      (fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD q 0)
      (n * n)⟩

/-- The flags after `i` query pairs are a segment of `n²` cells at `flg`. -/
theorem seg_aeStep (G : FlagsAt lim μ flg ab bc ac n F) (i : ℕ) :
    Seg (wrote μ flg
      (fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD q 0)
      (n * n)) flg (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i) := by
  intro q hq
  rw [length_aeStep, G.len] at hq
  rw [wrote_done hq, List.getD_eq_getElem]

/-- The weights are not touched by the flags. -/
theorem weights_wrote (C : Weights lim μ ab bc ac n U AB BC AC)
    (G : FlagsAt lim μ flg ab bc ac n F) (f : ℕ → ℤ) :
    Weights lim (wrote μ flg f (n * n)) ab bc ac n U AB BC AC := by
  light_facts C C.arrAB C.arrBC C.arrAC G
  exact
    { C with
      arrAB := C.arrAB.keep fun b hb => wrote_rest (by omega)
      arrBC := C.arrBC.keep fun b hb => wrote_rest (by omega)
      arrAC := C.arrAC.keep fun b hb => wrote_rest (by omega) }

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
/-- One query pair: a scan is made if the pair is accepted and its flag is 0. -/
theorem scanPairsAEStep_spec (hp : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (A : Answers lim μ out qa qb w n OUT QA QB)
    (hA : Apart flg (n * n) out w) (hQA : Apart flg (n * n) qa w) (hQB : Apart flg (n * n) qb w)
    (G : FlagsAt lim μ flg ab bc ac n F) (hd : d < lim.depth) (hc : c0 + len ≤ n) {i : ℕ}
    (hi : i < w) (idx res : ℤ) :
    Ends lim P d (scanPairsAEStep pScan)
      (scanPairsAEState μ out qa qb w flg ab bc ac n c0 len OUT AB BC AC F QA QB i i idx res)
      (60 + if aeExec (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i then
        tScanCallAE len else 0)
      fun σ' => ∃ idx' res', σ' = scanPairsAEState μ out qa qb w flg ab bc ac n c0 len OUT AB BC AC
        F QA QB (i + 1) i idx' res' := by
  light_facts C C.arrAB C.arrBC C.arrAC
  light_facts A A.arrOUT A.arrQA A.arrQB
  light_facts G
  set μ₁ := wrote μ flg
    (fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD q 0)
    (n * n) with hμ₁
  have hreadOUT : μ₁ (out + i) = OUT.getD i 0 := by
    rw [hμ₁, wrote_rest (by omega)]; exact A.arrOUT.read hi
  have hreadQA : μ₁ (qa + i) = (QA.getD i 0 : ℕ) := by
    rw [hμ₁, wrote_rest (by omega)]; exact A.arrQA.read hi
  have hreadQB : μ₁ (qb + i) = (QB.getD i 0 : ℕ) := by
    rw [hμ₁, wrote_rest (by omega)]; exact A.arrQB.read hi
  have ha := A.arrQA.getD_lt hi
  have hb := A.arrQB.getD_lt hi
  have hidx : idxOf n QA QB i < n * n := Nat.mul_add_lt_mul ha hb
  have hlenS : idxOf n QA QB i <
      (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).length := by
    rw [length_aeStep, G.len]; exact hidx
  have hreadF : μ₁ (flg + idxOf n QA QB i) =
      (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i).getD
        (idxOf n QA QB i) 0 := by
    rw [hμ₁, wrote_done hidx]
  have C₁ := weights_wrote C G (fun q => (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len)
    (idxOf n QA QB) F i).getD q 0)
  unfold scanPairsAEStep scanPairsAEState
  rw [← hμ₁, aeStep_succ, aePair, aeExec, accOf, hitOf]
  generalize hS : aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i = S
    at hreadF hμ₁ hlenS ⊢
  generalize hcell : S.getD (idxOf n QA QB i) 0 = cell at hreadF ⊢
  generalize OUT.getD i 0 = answer at hreadOUT ⊢
  unfold idxOf at hidx hreadF hlenS ⊢
  generalize QA.getD i 0 = a at hreadQA ha hidx hreadF hlenS ⊢
  generalize QB.getD i 0 = b at hreadQB hb hidx hreadF hlenS ⊢
  have haddr : ((flg : ℤ) + ((a : ℤ) * (n : ℤ) + (b : ℤ))).toNat = flg + (a * n + b) := by
    rw [show (flg : ℤ) + ((a : ℤ) * (n : ℤ) + (b : ℤ)) = ((flg + (a * n + b) : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast]
  -- if out[i] = 0
  by_cases hz : answer = 0
  · refine Ends.iteLast (fun _ => Ends.skip ⟨idx, res, ?_⟩)
      (fun h => absurd (by simp [hreadOUT, hz]) h) (by light_side)
    rw [hμ₁]
    simp [hz]
  refine Ends.iteLast (fun h => absurd h (by simp [hreadOUT, hz])) (fun _ => ?_) (by light_side)
  -- idx := flg + qa[i] n + qb[i]
  light_set (flg + (a * n + b) : ℕ) using hreadQA, hreadQB
  -- if M idx = 0
  by_cases hcell0 : cell = 0
  · refine Ends.iteLast (fun _ => ?_) fun h => absurd (by simp [haddr, hreadF, hcell0]) h
    -- res := scan(ab, bc, ac, n, qa[i], qb[i], c0, len); M idx := res
    light_call (scan_meets hp C₁ ha hb hc) using hreadQA, hreadQB, hz, hcell0, tScanCallAE with
      _ _ ⟨rfl, rfl⟩
    rw [flag_eq_bit]
    light_store (flg + (a * n + b) : ℕ) (bit (scanHit n AB BC AC a b c0 len)) using hz, hcell0,
      tScanCallAE
    refine ⟨(flg + (a * n + b) : ℕ), bit (scanHit n AB BC AC a b c0 len), ?_⟩
    rw [ite_eq_left ⟨decide_eq_true hz, hcell0⟩]
    congr 1
    funext y
    by_cases hy : y = flg + (a * n + b)
    · subst hy
      rw [Function.update_self, wrote_done hidx, getD_set_self _ hlenS]
    · rw [Function.update_of_ne hy, hμ₁]
      by_cases hin : Inside flg (n * n) y
      · obtain ⟨q, rfl⟩ : ∃ q, y = flg + q := ⟨y - flg, by omega⟩
        rw [wrote_done (by omega), wrote_done (by omega), getD_set_ne _ (by omega)]
      · have hout : Outside flg (n * n) y := by simp only [Inside, Outside] at hin ⊢; omega
        rw [wrote_rest hout, wrote_rest hout]
  · refine Ends.iteLast (fun h => absurd h (by simp [haddr, hreadF, hcell0])) fun _ =>
      Ends.skip ⟨(flg + (a * n + b) : ℕ), res, ?_⟩
    rw [hμ₁]
    simp [hcell0]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
/-- The time of the rounds, added up. -/
theorem sum_scanPairsAE_rounds (acc hit : ℕ → Bool) (idx : ℕ → ℕ) (F : List ℤ) (len w : ℕ) :
    ∑ i ∈ Finset.range w, (4 + (64 + if aeExec acc hit idx F i then tScanCallAE len else 0))
      = 68 * w + tScanCallAE len * aeExecs acc hit idx F w := by
  induction w with
  | zero => simp [aeExecs]
  | succ w ih =>
    rw [Finset.sum_range_succ, ih, aeExecs_succ]
    split_ifs <;> ring

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean
/-- **scanPairsAE** treats the `w` query pairs of an instance: the flags become
`aeStep … F w`, no other cell changes, and the time depends on the number of scans that are made. -/
theorem scanPairsAE_spec (hp : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (A : Answers lim μ out qa qb w n OUT QA QB)
    (hA : Apart flg (n * n) out w) (hQA : Apart flg (n * n) qa w) (hQB : Apart flg (n * n) qb w)
    (G : FlagsAt lim μ flg ab bc ac n F) (hd : d < lim.depth) (hc : c0 + len ≤ n) :
    Ends lim P d (scanPairsAEBody pScan)
      ⟨frame [out, qa, qb, w, flg, ab, bc, ac, n, c0, len], μ⟩
      (tScanPairsAE w len (aeExecs (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB)
        F w)) fun σ' =>
      Seg σ'.mem flg (aeStep (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F w) ∧
        SameOutside μ σ'.mem flg (n * n) := by
  light_facts C C.arrAB C.arrBC C.arrAC
  light_facts A A.arrOUT A.arrQA A.arrQB
  light_facts G
  have hsum := sum_scanPairsAE_rounds (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB)
    F len w
  unfold tScanPairsAE tAnswersAE
  -- i := 0
  light_set (0 : ℕ)
  -- while i < w
  refine (Ends.while (fun i σ => ∃ idx res, σ = scanPairsAEState μ out qa qb w flg ab bc ac n c0
    len OUT AB BC AC F QA QB i i idx res) w
    (fun i => 64 + if aeExec (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (idxOf n QA QB) F i then
      tScanCallAE len else 0) ?start ?round ?done).mono
    (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega) fun _ h => h
  case start =>
    have hmem : μ = wrote μ flg (fun q => F.getD q 0) (n * n) := by
      funext y
      by_cases hin : Inside flg (n * n) y
      · obtain ⟨q, rfl⟩ : ∃ q, y = flg + q := ⟨y - flg, by omega⟩
        rw [wrote_done (by omega), G.seg.getD (by rw [G.len]; omega)]
      · rw [wrote_rest (by simp only [Inside, Outside] at hin ⊢; omega)]
    refine ⟨0, 0, ?_⟩
    simp only [scanPairsAEState, aeStep_zero, ← hmem]
    simpa using (frame_append_zeros [(out : ℤ), qa, qb, w, flg, ab, bc, ac, n, c0, len, 0] 2).symm
  case round =>
    rintro i _ hi ⟨idx, res, rfl⟩
    refine ⟨by simp, by simp [scanPairsAEState]; omega, ?_⟩
    -- the query pair number i; then i := i + 1
    refine Ends.next _ ((scanPairsAEStep_spec hp C A hA hQA hQB G hd hc hi idx res).mono le_rfl
      ?_) (by omega)
    rintro _ ⟨idx', res', rfl⟩
    unfold scanPairsAEState
    light_set (i + 1 : ℕ)
    exact ⟨idx', res', rfl⟩
  case done =>
    rintro _ ⟨idx, res, rfl⟩
    refine ⟨by simp, by simp [scanPairsAEState], seg_aeStep G w, ?_⟩
    simp only [scanPairsAEState]
    exact sameOutside_wrote le_rfl

end

end Light.Sec3
