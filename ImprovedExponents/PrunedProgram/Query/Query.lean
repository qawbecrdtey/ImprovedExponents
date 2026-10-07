module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Program
public import ImprovedExponents.PrunedProgram.Pre.Defs
public import ImprovedExponents.PrunedProgram.Query.QuerySum

@[expose] public section

/-!
# A query, from the block that holds the data structure on pruned encodings

Upstream's `queryAt_spec` proves the routine `queryAtBody` (procedure 55: the sizes and the bands
from the directory, the areas, the digits of the output string by `outDigits`, the sum of Lemma 28
by `queryCore`) under `DSReady`, which holds the encodings of all bands as full segments.  Of the
data structure, the routine reads the directory, the tables, the roots, the tries and — in
`queryCore` only — the cells of the leaves of order below `t` contributing to the output string of
the position, which have at most `m` symbols `P₀`.  So the routine is correct under `DSReadyP`,
where the encodings are right at these leaves only: `queryAtP_spec` is `queryAt_spec` with
`DSReadyP` in the pre- and postcondition and `QueryCoreSpecP` (`queryCoreP_spec`) in place of
`QueryCoreSpec`; the body and the time are upstream's.  The parts of the proof that do not read
the data structure (`queryAtAreas_spec`, `coreArgs`, `coreArgs_value`, …) are reused; those that
do are copied with `DSReadyP` in place of `DSReady`, under the same names with a `P`.

`queryAtP_of_base58` discharges the assumptions for every program `base58 ++ R` that begins with
upstream's 58 procedures, as upstream's `queryAt_base58`.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean`, `Directory.lean`,
`Areas.lean`, `Routines.lean` and `Program.lean` (Apache-2.0).
-/

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

section Proof

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The first part -/

/-- The first part reads the sizes, the addresses of the tables, and the two bands. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAtReads_spec)
theorem queryAtReadsP_spec (hlim : Lim30 lim p t b0 U) (hds : DSReadyP p t hmL aX aY b0 X Y μ)
    {I J : ℕ} (hI : I < p.N) (hJ : J < p.N) :
    Ends lim P d queryAtReads ⟨frame [(I : ℤ), (J : ℤ), (b0 : ℤ)], μ⟩ 90
      (· = ⟨frame (queryAtRead p t b0 I J), μ⟩) := by
  have hw := hlim.std.space_le
  have hdir : b0 + 31 < lim.space ∧ p.aBAND b0 + p.N ≤ lim.space := by
    have := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have dir := hds.shared.dirCells
  have cellT : μ ((b0 : ℤ) + 31).toNat = (t : ℕ) :=
    (congrArg μ (toNat_natCast_add_natCast b0 31)).trans hds.cellT
  have bandI := hds.shared.band I hI
  have bandJ := hds.shared.band J hJ
  -- levels := dir[0]; inner := dir[1]; switch := dir[31]; outer := dir[4]
  light_set (p.L : ℕ) using dir.levels
  light_set (p.m : ℕ) using dir.inner
  light_set (t : ℕ) using cellT
  light_set (p.Lo : ℕ) using dir.outer
  -- blocks := dir[7]; bands := dir[9]; leaves := dir[10]
  light_set (p.K0 : ℕ) using dir.blocks
  light_set (p.nB : ℕ) using dir.bands
  light_set (p.T : ℕ) using dir.leaves
  -- bandTab := dir[22]; blockTab := dir[23]; digitTab := dir[24]; digits := dir[30]
  light_set (p.aBAND b0 : ℕ) using dir.band
  light_set (p.aBLOCK b0 : ℕ) using dir.block
  light_set (p.aDIG3 b0 : ℕ) using dir.digits
  light_set (aWD p b0 : ℕ) using dir.sharedEnd
  -- bandI := bandTab[I]; bandJ := bandTab[J]
  light_set (I / (p.K0 * p.N0) : ℕ) using bandI
  light_set (J / (p.K0 * p.N0) : ℕ) using bandJ
  rfl

/-! ## The call of outDigits -/

/-- The block holds what outDigits assumes. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (outArgs_pre)
theorem outArgsP_pre (hlim : Lim30 lim p t b0 U) (hds : DSReadyP p t hmL aX aY b0 X Y μ)
    {I J : ℕ} (hI : I < p.N) (hJ : J < p.N) : OutDigitsPre lim μ (outArgs p b0 I J) := by
  have hgI : I / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hgJ : J / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hidx : I / p.N0 % p.K0 * p.K0 + J / p.N0 % p.K0 < p.KK := Nat.mul_add_lt_mul hgI hgJ
  -- the three tables lie below WD, and WD inside the memory
  have hsp := hlim.space
  have hmaskI := Nat.mul_add_le_mul hidx (le_refl p.L)
  have hrowI := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have hrowJ := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have hLo : p.L - p.m = p.Lo := rfl
  obtain ⟨⟩ := areas p t b0
  refine
    { std := hlim.std
      m_le := hmL
      gI_lt := hgI
      gJ_lt := hgJ
      index_lt := tableIndex_lt p.L p.m (⟨_, hgI⟩, ⟨_, hgJ⟩)
      segMask := segN_of_segB (hds.shared.mask _ hidx)
      segI := hds.shared.dig3 I hI
      segJ := hds.shared.dig3 J hJ
      lenI := length_digitList ..
      lenJ := length_digitList ..
      ltI := fun _ => lt_of_mem_digitList (by norm_num)
      ltJ := fun _ => lt_of_mem_digitList (by norm_num)
      spaceMasks := by change p.aMASK b0 + p.KK * p.L < lim.space; omega
      apartMask := ?_
      apartI := ?_
      apartJ := ?_
      spaceI := ?_
      spaceJ := ?_
      spaceDest := ?_ }
  -- the six fields that are left: the tables lie apart from WD, and all within the memory
  all_goals
    simp only [outArgs, OutDigitsArgs.base]
    omega

/-- The third part writes the digits of the output string of (I, J) at WD. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAtOut_spec)
theorem queryAtOutP_spec (hOut : OutDigitsSpec lim P) (hlim : Lim30 lim p t b0 U)
    (hds : DSReadyP p t hmL aX aY b0 X Y μ) {I J : ℕ} (hI : I < p.N) (hJ : J < p.N)
    (hd : d + 1 ≤ lim.depth) :
    Ends lim P d queryAtOut ⟨frame (queryAtLocals p t b0 I J), μ⟩ (tOutDigits p.L + 40) fun σ' =>
      ∃ (r : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ'⟩ ∧
        SegN μ' (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J)) ∧
        SameOutside μ μ' (aWD p b0) p.L := by
  have hw := hlim.std.space_le
  have hpre := outArgsP_pre hlim hds hI hJ
  have blockI := hds.shared.block I hI
  have blockJ := hds.shared.block J hJ
  have hsp := hlim.space
  have hrowI := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have hrowJ := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have hbound : b0 + 31 < lim.space ∧ p.aBLOCK b0 + p.N ≤ lim.space ∧
      p.aDIG3 b0 + p.N * p.Lo ≤ lim.space := by
    obtain ⟨⟩ := areas p t b0
    omega
  have hprodI : ((p.aDIG3 b0 + I * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.aDIG3 b0 + I * p.Lo ≤ lim.space)
  have hprodJ : ((p.aDIG3 b0 + J * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.aDIG3 b0 + J * p.Lo ≤ lim.space)
  have hI0 : (0 : ℤ) ≤ (I : ℤ) * p.Lo := by positivity
  have hJ0 : (0 : ℤ) ≤ (J : ℤ) * p.Lo := by positivity
  push_cast at hprodI hprodJ
  -- outDigits(blockTab[I], blockTab[J], digitTab + I (L - m), digitTab + J (L - m), dir[21], …)
  light_call (hOut _ μ hpre) using queryAtLocals, queryAtRead, outArgs, blockI, blockJ,
    hds.shared.dirCells.mask with r μ' h
  refine ⟨r, μ', rfl, ?_, h.2⟩
  rw [digitsO_outStrOfPos]
  exact h.1

/-! ## The call of queryCore -/

/-- The block, with the digits of the output string at WD, holds what queryCore assumes of pruned
encodings: the encodings of the two bands are right at the leaves with at most m symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (coreArgs_pre)
theorem coreArgsP_pre (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hds : DSReadyP p t hmL aX aY b0 X Y μ) (I J : Fin p.N)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    QueryCorePreP lim μ (coreArgs p t hmL b0 X Y I J) := by
  have hU : 0 ≤ U := (abs_nonneg _).trans (hX I ⟨0, Nat.pow_pos (by norm_num)⟩)
  have hβ : (I : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N I I.isLt
  have hβ' : (J : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N J J.isLt
  -- the encodings lie below WD, the tries behind the scratch strings
  have hsp := hlim.space
  have hlen := length_dsTries_le p t hmL X Y
  have hrowA := Nat.mul_add_le_mul hβ (le_refl p.T)
  have hrowB := Nat.mul_add_le_mul hβ' (le_refl p.T)
  have hT : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  refine
    { std := hlim.std
      t_le := ht
      card := card_innerSetO_outStrOfPos (stdLayout hmL) I J
      segA := hds.shared.encA _ hβ
      segB := hds.shared.encB _ hβ'
      segT := hds.trie
      segDigits := hwd
      walk := coreArgs_walk I J ht
      sums := coreArgs_sums I J ht hlim hU hX hY
      prod := abs_enc_mul_le hlim hU hX hY _ _
      pow := hlim.pow_le
      ss_wd := ?_
      box_wd := ?_
      ss_box := ?_
      ss_aA := ?_
      ss_aB := ?_
      box_aA := ?_
      box_aB := ?_
      ss_tr := ?_
      box_tr := ?_
      aA_lt := ?_
      aB_lt := ?_
      tr_lt := ?_
      wd_lt := ?_
      ss_lt := ?_
      box_lt := ?_ }
  -- the fifteen fields that are left: the areas lie apart from each other and within the memory
  all_goals
    simp only [coreArgs]
    omega

/-- The fourth part returns (XY)[I, J] and changes the scratch strings BOX and SS only. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAtCore_spec)
theorem queryAtCoreP_spec (hCore : QueryCoreSpecP lim P) (ht : t ≤ p.m)
    (hlim : Lim30 lim p t b0 U) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U)
    (hds : DSReadyP p t hmL aX aY b0 X Y μ) (I J : Fin p.N) (hd : d + 2 ≤ lim.depth) (r : ℤ)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    Ends lim P d queryAtCore ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ⟩
      (tQueryCore p.L p.m t + 60) fun σ' =>
        σ'.loc 0 = (X * Y) I J ∧ SameOutside2 μ σ'.mem (aSS p b0) p.m (aBOX p b0) p.L := by
  have hw := hlim.std.space_le
  have hpre := coreArgsP_pre ht hlim hX hY hds I J hwd
  have hvalue := coreArgs_value (hmL := hmL) (b0 := b0) (X := X) (Y := Y) I J ht
  have dir := hds.shared.dirCells
  have htile := tileOf_lt I J hmL
  have cellRoot : μ (aROOTS p b0 + tileOf p I J)
      = ((dsTries p t hmL X Y).root (tileOf p I J) : ℕ) :=
    hds.roots.read (by rw [length_dsTries_roots]; exact htile)
  have hdir : b0 + 31 < lim.space ∧ aROOTS p b0 + p.nB * p.nB < lim.space := by
    have hsp := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have hmeets := (hCore _ μ hpre _ (by omega))
  have hencA := hpre.aA_lt
  have hencB := hpre.aB_lt
  simp only [coreArgs, tileOf] at hmeets hvalue hencA hencB htile cellRoot
  unfold queryAtLocals queryAtRead
  -- the bands, the root and 10^L become variables; the products in the arguments, in the integers
  generalize 10 ^ p.L = leaves at hencA hencB
  generalize (I : ℕ) / (p.K0 * p.N0) = β at *
  generalize (J : ℕ) / (p.K0 * p.N0) = β' at *
  generalize (dsTries p t hmL X Y).root (β * p.nB + β') = root at *
  have hencA' : ((p.aENCA b0 + β * p.T : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
  have hencB' : ((p.aENCB b0 + β' * p.T : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
  have hroot' : ((aROOTS p b0 + (β * p.nB + β') : ℕ) : ℤ) < lim.space := by
    exact_mod_cast (by omega)
  have hrow0 : (0 : ℤ) ≤ (β : ℤ) * p.T := by positivity
  have hcol0 : (0 : ℤ) ≤ (β' : ℤ) * p.T := by positivity
  have hband0 : (0 : ℤ) ≤ (β : ℤ) * p.nB := by positivity
  have haddr : ((aROOTS p b0 : ℤ) + ((β : ℤ) * p.nB + β')).toNat
      = aROOTS p b0 + (β * p.nB + β') := by exact_mod_cast Int.toNat_natCast _
  push_cast at hencA' hencB' hroot'
  -- queryCore(dir[26] + bandI 10^L, dir[27] + bandJ 10^L, tries, roots[bandI nB + bandJ], …)
  light_call hmeets using dir.encA, dir.encB, haddr, cellRoot with r' μ' h
  refine ⟨?_, h.2⟩
  simp only [setLocal, List.cons_append, frame, List.getD_cons_zero]
  rw [h.1, hvalue]

/-! ## The routine -/

/-- **queryAt** meets its specification on pruned encodings: upstream's routine, under the
assumption that the encodings of the bands are right at the leaves with at most `m` symbols `P₀`
only. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAt_spec)
theorem queryAtP_spec (hP : P[Proc.queryAt]? = some queryAtBody) (hOut : OutDigitsSpec lim P)
    (hCore : QueryCoreSpecP lim P) : QueryAtSpecP lim P := by
  intro p t hmL aX aY b0 X Y U μ I J ht hlim hX hY hds
  refine fun d hd => ⟨queryAtBody, hP, ?_⟩
  unfold tQueryAt
  -- the sizes, the tables, the bands
  light_piece (queryAtReadsP_spec hlim hds I.isLt J.isLt) with _ rfl
  -- the areas
  light_piece (queryAtAreas_spec hlim I J) with _ rfl
  -- the digits of the output string, which change WD only
  light_piece (queryAtOutP_spec hOut hlim hds I.isLt J.isLt (by omega))
    with _ ⟨r, μ₁, rfl, hwd, same₁⟩
  have same₁' : SameOutside μ μ₁ (aWD p b0) (3 * p.L + p.m) := same₁.mono le_rfl (by omega)
  -- the sum of Lemma 28, which changes BOX and SS only
  light_piece (queryAtCoreP_spec hCore ht hlim hX hY (hds.of_same same₁') I J (by omega) r hwd)
    with ⟨loc₂, μ₂⟩ ⟨hr, same₂⟩
  have same₂' : SameOutside μ μ₂ (aWD p b0) (3 * p.L + p.m) := by
    obtain ⟨⟩ := areas p t b0
    exact same₁'.then same₂ fun b hb => ⟨hb, by omega, by omega⟩
  exact ⟨hr, hds.of_same same₂', same₂'⟩

end Proof

/-! ## The routine in a program that holds the routines of Section 4 -/

/-- `queryCore` on pruned encodings, in every program that holds the routines of Section 4 at
their numbers. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Routines.lean (specs40)
theorem queryCoreSpecP_of {lim : Limits} {P : Program} (h : Has40 P) (hs : Std lim) :
    QueryCoreSpecP lim P :=
  have S := specs40 h hs
  queryCoreP_spec (h 13 (by omega)) ⟨S.nineFirst, S.nineNext, S.scatter, S.horner, S.lookup⟩

/-- A query at a given place of the memory on pruned encodings, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Routines.lean (queryAtSpec_all)
theorem queryAtSpecP_all {P : Program} (h : Has40 P)
    (h55 : P[Proc.queryAt]? = some queryAtBody) : ∀ lim, QueryAtSpecP lim P :=
  fun _ p t hmL aX aY b0 X Y U μ I J ht hlim =>
    queryAtP_spec h55 (specs40 h hlim.std).outDigits (queryCoreSpecP_of h hlim.std)
      p t hmL aX aY b0 X Y U μ I J ht hlim

/-- **A query at a given place of the memory on pruned encodings**, in every program that begins
with upstream's 58 procedures. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (queryAt_base58)
theorem queryAtP_of_base58 {lim : Limits} {P R : Program} (hP : P = base58 ++ R) :
    QueryAtSpecP lim P := by
  subst hP
  exact queryAtSpecP_all (has40_base58 R) (at_base58 rfl R) lim

end Light.Sec4
