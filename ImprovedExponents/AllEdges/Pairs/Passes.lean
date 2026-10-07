module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Lang.Frames
public import ThreeSumApsp.Spec.Sec3.Problems

@[expose] public section

/-!
# Two loops over arrays for the reduction from all pairs to all-edges Exact Triangle

The host `pairsAE` (`ImprovedExponents.AllEdges.Pairs.Host`) asks a solver of all-edges Exact
Triangle `2b + 3` questions and takes, cell by cell, the disjunction of the answers; one of the
three matrices of a question is a transpose.  The two loops of this file do these two things.

* or(len, f, out) replaces out[i] by out[i] + f[i] − out[i] f[i] for i < len: the disjunction of
  two flags, in at most 31 len + 6 steps (`or_meets`; the pattern is upstream's `bump`).
* transpose(n, src, c, dst) writes src[i n + j] + c to dst[j n + i] for i, j < n, in at most
  30 n² + 20 n + 6 steps (`transpose_meets`): a loop over the columns j, whose body is a pass over
  the row j of the destination.
-/

namespace ImprovedExponents.AllEdges

open Light ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The disjunction of two arrays of flags -/

namespace OrPass

/-- The number of cells. -/
abbrev Len : ℕ := 0
/-- The address of the flags that are read. -/
abbrev Flags : ℕ := 1
/-- The address of the flags that are changed. -/
abbrev Dest : ℕ := 2
/-- The counter. -/
abbrev Index : ℕ := 3

end OrPass

open OrPass in
/-- or(len, f, out): for i < len, out[i] := out[i] + f[i] − out[i] · f[i]. -/
def orBody : Stmt :=
  pass Index (v Len) (v Dest)
    (M (v Dest +' v Index) +' M (v Flags +' v Index) -'
      M (v Dest +' v Index) *' M (v Flags +' v Index))

/-- The disjunction of two lists of flags, cell by cell. -/
def orL (L F : List ℤ) : List ℤ := List.zipWith (fun o f => o + f - o * f) L F

@[simp] theorem length_orL (L F : List ℤ) : (orL L F).length = min L.length F.length := by
  simp [orL]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/Passes.lean (bump_meets)
/-- **or** replaces the flags at out by their disjunction with the flags at f, and changes nothing
else.  All flags are 0 or 1. -/
theorem or_meets {p : ℕ} (hp : P[p]? = some orBody) {μ : ℕ → ℤ} {fl out len : ℕ} {F L : List ℤ}
    (hF : Seg μ fl F) (hL : Seg μ out L) (hlen : F.length = len ∧ L.length = len)
    (hsep : Apart fl len out len)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ fl + len ≤ lim.space ∧ out + len ≤ lim.space)
    (hflag : ∀ f ∈ F, f = 0 ∨ f = 1) (hL01 : ∀ o ∈ L, o = 0 ∨ o = 1) (hw : 1 ≤ lim.word) :
    Meets lim P p d [(len : ℤ), fl, out] μ (31 * len + 6) fun _ μ' =>
      Seg μ' out (orL L F) ∧ SameOutside μ μ' out len := by
  obtain ⟨lF, lL⟩ := hlen
  obtain ⟨hsp, hfl, hout⟩ := hlim
  set f : ℕ → ℤ := fun i => L.getD i 0 + F.getD i 0 - L.getD i 0 * F.getD i 0 with hf
  have hfi : ∀ i (hF : i < F.length) (hL : i < L.length), f i = L[i] + F[i] - L[i] * F[i] :=
    fun i hF hL => by
      rw [hf]
      simp only [List.getD_eq_getElem _ _ hF, List.getD_eq_getElem _ _ hL]
  refine .of_body hp (Ends.pass f (fun j hj => ?_) ?_ hsp hout rfl rfl)
  · -- round j reads f[j], which is never written, and out[j], which it then overwrites
    have hreadF : wrote μ out f j (fl + j) = F[j] :=
      (wrote_rest (by omega)).trans (hF j (by omega))
    have hreadL : wrote μ out f j (out + j) = L[j] :=
      (wrote_rest (by omega)).trans (hL j (by omega))
    rw [update_frame_setLocal]
    rcases hflag _ (List.getElem_mem (show j < F.length by omega)) with h | h <;>
    rcases hL01 _ (List.getElem_mem (show j < L.length by omega)) with h' | h'
    all_goals
      simp [Limits.Addr, abs_le, hreadF, hreadL, hfi j (by omega) (by omega), h, h']; omega
  · dsimp only
    refine ⟨seg_wrote (by simp [orL, lF, lL]) fun i hi => ?_, sameOutside_wrote le_rfl⟩
    simp only [orL, List.length_zipWith] at hi ⊢
    rw [List.getElem_zipWith]
    exact (hfi i (by omega) (by omega)).symm

/-- The disjunction of the flags is a flag. -/
theorem orL_mem {L F : List ℤ} (hL : ∀ o ∈ L, o = 0 ∨ o = 1) (hF : ∀ f ∈ F, f = 0 ∨ f = 1) :
    ∀ z ∈ orL L F, z = 0 ∨ z = 1 := by
  intro z hz
  simp only [orL] at hz
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hz
  rw [List.length_zipWith] at hi
  rw [List.getElem_zipWith]
  rcases hL _ (List.getElem_mem (show i < L.length by omega)) with h | h <;>
    rcases hF _ (List.getElem_mem (show i < F.length by omega)) with h' | h' <;> simp [h, h']

/-! ## The transpose -/

namespace Transpose

/-- The side n of the matrix. -/
abbrev Side : ℕ := 0
/-- The address of the source. -/
abbrev Src : ℕ := 1
/-- The summand c. -/
abbrev Shift : ℕ := 2
/-- The address of the destination. -/
abbrev Dst : ℕ := 3
/-- The column j of the source. -/
abbrev Col : ℕ := 4
/-- The address of the row j of the destination. -/
abbrev Row : ℕ := 5
/-- The row i of the source. -/
abbrev Idx : ℕ := 6

end Transpose

open Transpose in
/-- The row j of the destination: for i < n, dst[j n + i] := src[i n + j] + c. -/
def transposeRow : Stmt :=
  .set Row (v Dst +' v Col *' v Side) ;;
  pass Idx (v Side) (v Row) (M (v Src +' v Idx *' v Side +' v Col) +' v Shift)

open Transpose in
/-- transpose(n, src, c, dst): for j < n, the row j of the destination. -/
def transposeBody : Stmt := .for Col (v Side) transposeRow

/-- The transpose of the `n × n` matrix `Y` (entry `(k, j)` at `k n + j`) with `c` added: cell
`q = j n + k` holds `Y[k n + j] + c`. -/
def transposeL (n : ℕ) (c : ℤ) (Y : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q => Y.getD (q % n * n + q / n) 0 + c

@[simp] theorem length_transposeL (n : ℕ) (c : ℤ) (Y : List ℤ) :
    (transposeL n c Y).length = n * n := by
  simp [transposeL]

/-- The entry `(j, k)` of the transpose. -/
theorem transposeL_getD {n : ℕ} (c : ℤ) (Y : List ℤ) {j k : ℕ} (hj : j < n) (hk : k < n) :
    (transposeL n c Y).getD (j * n + k) 0 = Y.getD (k * n + j) 0 + c := by
  have hq : j * n + k < n * n := by nlinarith
  have hdiv : (j * n + k) / n = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk]
    simp
  have hmod : (j * n + k) % n = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  simp only [transposeL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
    Option.map_some, Option.getD_some, hdiv, hmod]

/-- The entries of the transpose of a matrix with entries in `[-U, U]`, with `c` added, lie in
`[c - U, c + U]`. -/
theorem mem_transposeL_bounds {n : ℕ} {Y : List ℤ} {U : ℤ} (hY : AbsLe Y U)
    (hlen : Y.length = n * n) (c : ℤ) : ∀ z ∈ transposeL n c Y, c - U ≤ z ∧ z ≤ c + U := by
  intro z hz
  simp only [transposeL, List.mem_map, List.mem_range] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  have hn : 0 < n := by rcases n with _ | n <;> simp_all
  have hidx : q % n * n + q / n < n * n := by
    have h1 := Nat.mod_lt q hn
    have h2 : q / n < n := by rwa [Nat.div_lt_iff_lt_mul hn]
    nlinarith
  have hmem : Y.getD (q % n * n + q / n) 0 ∈ Y := by
    rw [List.getD_eq_getElem _ _ (hlen ▸ hidx)]
    exact List.getElem_mem _
  have := abs_le.1 (hY _ hmem)
  constructor <;> omega

/-- A bound on the entries of the transpose. -/
theorem absLe_transposeL {n : ℕ} {Y : List ℤ} {U : ℤ} (hY : AbsLe Y U) (hlen : Y.length = n * n)
    {c B : ℤ} (hlo : -B ≤ c - U) (hhi : c + U ≤ B) : AbsLe (transposeL n c Y) B := fun z hz => by
  have := mem_transposeL_bounds hY hlen c z hz
  exact abs_le.2 ⟨by omega, by omega⟩

/-- The memory after the rows `0, …, j - 1` of the transpose have been written. -/
private def tMem (μ : ℕ → ℤ) (dst n : ℕ) (c : ℤ) (Y : List ℤ) (j : ℕ) : ℕ → ℤ :=
  wrote μ dst (fun q => (transposeL n c Y).getD q 0) (j * n)

/-- The row `j` written on top of the rows below it. -/
private theorem tMem_succ {μ : ℕ → ℤ} {dst n : ℕ} {c : ℤ} {Y : List ℤ} {j : ℕ} (hj : j < n) :
    wrote (tMem μ dst n c Y j) (dst + j * n) (fun i => Y.getD (i * n + j) 0 + c) n =
      tMem μ dst n c Y (j + 1) := by
  funext a
  simp only [tMem, wrote, Nat.succ_mul]
  by_cases h1 : dst + j * n ≤ a ∧ a < dst + j * n + n
  · rw [ite_eq_left h1, ite_eq_left (by omega)]
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < n ∧ a = dst + (j * n + i) :=
      ⟨a - dst - j * n, by omega, by omega⟩
    rw [show dst + (j * n + i) - (dst + j * n) = i by omega, Nat.add_sub_cancel_left,
      transposeL_getD c Y hj hi]
  · rw [ite_eq_right h1]
    by_cases h2 : dst ≤ a ∧ a < dst + j * n
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- **transpose** writes the transpose of the matrix at src, with c added to every entry, to the n²
cells from dst, and changes nothing else. -/
theorem transpose_meets {p : ℕ} (hp : P[p]? = some transposeBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    {c : ℤ} {Y : List ℤ} (hY : Seg μ src Y) (hlen : Y.length = n * n)
    (hsep : Apart src (n * n) dst (n * n))
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ src + n * n ≤ lim.space ∧ dst + n * n ≤ lim.space)
    (hfits : ∀ y ∈ Y, |y + c| ≤ lim.word) :
    Meets lim P p d [(n : ℤ), src, c, dst] μ (30 * (n * n) + 20 * n + 6) fun _ μ' =>
      Seg μ' dst (transposeL n c Y) ∧ SameOutside μ μ' dst (n * n) := by
  obtain ⟨hsp, hsrc, hdst⟩ := hlim
  have hn : (n : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (Nat.le_mul_self n).trans (by omega : n * n ≤ lim.space)) hsp
  refine .of_body hp ?_
  simp only [transposeBody]
  refine Ends.forShape (fun j (s : ℤ × ℤ) μ' => ⟨frame [n, src, c, dst, j, s.1, s.2], μ'⟩)
    (fun j μ' => μ' = tMem μ dst n c Y j) n (30 * n + 11) (0, 0) (by simp [tMem, wrote_zero])
    ?round ?done
    (first := by
      rw [update_frame_setLocal]
      exact congrArg (State.mk · μ) (frame_append_zeros _ 2).symm)
    (hT := by simp; nlinarith)
  case round =>
    rintro j s μ' hj rfl
    have hjn : j * n + n ≤ n * n := by nlinarith
    simp only [transposeRow]
    -- Row := Dst + Col * Side
    light_set (dst + j * n : ℕ)
    refine Ends.pass (fun i => Y.getD (i * n + j) 0 + c) (fun i hi => ?_) ?_ hsp (by omega) rfl rfl
      (hT := by simp; omega)
    · -- round i reads src[i n + j], which is never written
      have hin : i * n + j < n * n := by nlinarith
      have hread : wrote (tMem μ dst n c Y j) (dst + j * n) (fun i => Y.getD (i * n + j) 0 + c) i
          (src + (i * n + j)) = Y.getD (i * n + j) 0 := by
        rw [wrote_rest (by omega), tMem, wrote_rest (by omega), hY.getD (hlen ▸ hin)]
      have hmem : Y.getD (i * n + j) 0 ∈ Y := by
        rw [List.getD_eq_getElem _ _ (hlen ▸ hin)]
        exact List.getElem_mem _
      have hfit := abs_le.1 (hfits _ hmem)
      have htoNat : ((src : ℤ) + (i : ℤ) * n + j).toNat = src + (i * n + j) := by omega
      simp only [List.getD_eq_getElem?_getD] at hread hfit
      rw [update_frame_setLocal]
      have hin' : ((i * n + j : ℕ) : ℤ) < ((n * n : ℕ) : ℤ) := by exact_mod_cast hin
      have hjn' : ((j * n + n : ℕ) : ℤ) ≤ ((n * n : ℕ) : ℤ) := by exact_mod_cast hjn
      push_cast at hin' hjn'
      simp only [Expr.Safe, Op.eval, Expr.val, frame, setLocal, Nat.cast_add, Nat.cast_mul,
        List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.lt_add_one, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
        Option.getD_some, Nat.ofNat_pos, true_and, Nat.one_lt_ofNat,
        List.getElem?_cons_succ, Nat.reduceLT, Limits.Addr, abs_le, htoNat, hread]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> first | omega | trivial
    · refine ⟨((dst + j * n : ℕ), n), tMem μ dst n c Y (j + 1), ?_, rfl⟩
      rw [update_frame_setLocal, tMem_succ hj]
      rfl
  case done =>
    rintro s μ' rfl
    refine ⟨fun i hi => ?_, show SameOutside μ (tMem μ dst n c Y n) dst (n * n) from
      sameOutside_wrote le_rfl⟩
    simp only [length_transposeL] at hi
    change wrote μ dst (fun q => (transposeL n c Y).getD q 0) (n * n) (dst + i) = _
    rw [wrote_done hi, List.getD_eq_getElem _ _ (by simpa using hi)]

end ImprovedExponents.AllEdges
