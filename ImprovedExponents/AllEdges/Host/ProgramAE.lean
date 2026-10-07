module

public import ImprovedExponents.AllEdges.Host.HostAE
public import ImprovedExponents.HostMid.NeedPolynomial

@[expose] public section

/-!
# The all-edges host solves all-edges Exact Triangle; the program, assembled

The specification of the core (`aeCore_spec`, as `ImprovedExponents.HostMid.et17_spec'`) and of the
top procedure (`aeTop_spec`), the list `aeProcs` of the procedures (the variant host's `et17Procs'`
with the all-edges procedures appended), and `ae17_solves`: with a solver of Lop-AE-SparseTri and
two parameter procedures, the program solves `aeTask` with the time `hostTimeAE` and the need
`hostNeedAE`, which stays polynomial (`hostNeedAE_poly`).
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec HostMid

variable {P₀ R : Program} {ν : Et17Nums} {pScanPairsAE pFill pBruteAE pLoopAE : ℕ}
  {Tn : List ℕ → ℕ} {need : List ℕ → Need} {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

/-! ## The core -/

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/ParametersStage.lean
open Et17 in
/-- **The small case**: the call of the all-edges brute force, which writes the flags at the free
pointer and returns it. -/
theorem aeSmall_spec
    (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeedCoreAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (.call pBruteAE [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free] 0)
      ⟨frame (et17LocA x fr D g), μ⟩ (tBruteAE x.n + 8)
      fun σ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧ σ'.loc 0 = flg ∧
        Seg σ'.mem flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ σ'.mem fr := by
  have hok' := hostNeedAt'_ok hok
  have hbrute : (bruteNeed x.n x.U).Ok lim fr (d + 1) :=
    hok'.mono (by simp only [bruteNeed, hostNeedAt', hostWord]; omega)
      (by simp only [bruteNeed]; omega) (by simp only [bruteNeed, hostNeedAt']; omega)
  have hdepth := hok.depth
  have hcells := hok.cells
  simp only [hostNeedCoreAt, hostNeedAt'] at hdepth hcells
  refine Ends.callTo (bruteAE_meets C.bruteAE C.base.loop.scan x μ fr hpre hbrute (by omega)) ?_
    (by simp [et17LocA])
  rintro _ _ ⟨rfl, hseg, hkept⟩
  exact ⟨fr, le_rfl, by omega, by simp [et17LocA], hseg, hkept⟩

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Correct.lean
/-- **The core of the all-edges host**: within `hostCoreTime`, it returns the address of the flags
of all-edges Exact Triangle, which lie at or above the free pointer; no cell below the free
pointer changes. -/
theorem aeCore_spec
    (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeedCore Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (aeCoreBody ν pBruteAE pLoopAE) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩
      (hostCoreTime Dfun Gfun tD tG Tn x.n x.U)
      fun σ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧ σ'.loc 0 = flg ∧
        Seg σ'.mem flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ σ'.mem fr := by
  have hok' : (hostNeed' Dfun Gfun wD wG need x.n x.U).Ok lim fr d := hostNeedAt'_ok hok
  have hparams := et17Params_spec' C.base x μ fr hpre hok'
  have hone : (1 : ℤ) ≤ lim.word := by
    have hword := hok.word
    simp only [hostNeedCore, hostNeedCoreAt, hostNeedAt', hostWord] at hword
    omega
  rw [← frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr] 29]
  unfold hostNeedCore at hok
  unfold aeCoreBody hostCoreTime hostSetup
  generalize Dfun x.n = D at *
  generalize Gfun D = g at *
  -- the parameters
  refine Ends.next _ (hparams.mono le_rfl ?_) (by omega)
  rintro _ rfl
  -- if n is small: the brute force
  by_cases hs : SmallCase x.n D g
  · rw [if_pos hs]
    exact Ends.iteLast (fun _ => (aeSmall_spec C x μ fr D g _ _ hpre hok).mono
      (by simp; omega) fun _ h => h) (fun h => absurd (by simp [et17LocA, hs]) h) (by simp; omega)
  rw [if_neg hs]
  refine Ends.iteLast (fun h => absurd h (by simp [et17LocA, hs])) (fun _ => ?_) (by simp; omega)
  -- otherwise: the sizes, then the tables and the loop over the instances
  have hbig := not_smallCase_iff.1 hs
  have htime := hostRunTimeAE_le hpre hbig Tn
  refine Ends.next _ ((et17Sizes_spec' C.base x μ fr D g _ _ hpre hbig (hostNeedAt'_ok hok)).mono
    le_rfl ?_) (by unfold hostMainAE; simp; omega)
  rintro _ ⟨μ', rfl, hk⟩
  refine (et17TablesAE_spec C x μ' fr D g _ _ (hpre.keep hk) hbig hok).mono
    (by unfold hostMainAE; simp; omega) ?_
  rintro σ'' ⟨flg, hfr, hsp, hres, hseg, hk'⟩
  exact ⟨flg, hfr, hsp, hres, hseg, fun a ha => (hk' a ha).trans (hk a ha)⟩

/-! ## The top procedure -/

/-- **The all-edges host decides all-edges Exact Triangle.**  In a program `P₀ ++ R` that
satisfies the context, with the core at `pCore` and `copy` at `pCopy`, on an instance with
`x.Pre μ fr` and within limits that allow for `hostNeedAE`, the top procedure ends within
`hostTimeAE` steps in a state that satisfies `aeTask.Post`. -/
theorem aeTop_spec {pCore pCopy : ℕ}
    (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG wD wG)
    (hCore : (P₀ ++ R)[pCore]? = some (aeCoreBody ν pBruteAE pLoopAE))
    (hCopy : (P₀ ++ R)[pCopy]? = some copyBody)
    (x : AeInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeedAE Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (aeTopBody pCore pCopy)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩
      (hostTimeAE Dfun Gfun tD tG Tn x.n x.U) fun σ' => aeTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hdepth := hok.depth
  have hcells := hok.cells
  have hw := hok.space
  simp only [hostNeedAE, hostNeedCore, hostNeedCoreAt, hostNeedAt'] at hdepth hcells
  have hok₁ : (hostNeedCore Dfun Gfun wD wG need x.n x.U).Ok lim fr (d + 1) :=
    hok.mono le_rfl le_rfl (by simp only [hostNeedAE]; omega)
  have hlay : 3 * (x.n * x.n) ≤ hostLayout x.n x.U (Dfun x.n) := by unfold hostLayout; omega
  have hout := hpre.belowOut
  unfold aeTopBody hostTimeAE
  -- flg := aeCore(n, U, ab, bc, ac, fr)
  have hcore : Ends lim (P₀ ++ R) (d + 1) (aeCoreBody ν pBruteAE pLoopAE)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ (hostCoreTime Dfun Gfun tD tG Tn x.n x.U)
      fun σ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧ σ'.loc 0 = flg ∧
        Seg σ'.mem flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ σ'.mem fr :=
    aeCore_spec C x.tri μ fr hpre.tri hok₁
  light_call (Meets.of_body (Q := fun r μ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧
      r = flg ∧ Seg μ' flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ μ' fr) hCore hcore)
    with r μ₁ ⟨flg, hfr, hsp, rfl, hseg, hkept⟩
  -- flg := copy(flg, out, n * n)
  have hn : ((x.n * x.n : ℕ) : ℤ) = (x.n : ℤ) * (x.n : ℤ) := by push_cast; rfl
  have hsep : Apart flg (x.n * x.n) x.out (x.n * x.n) := Or.inr (by omega)
  refine Ends.callTo (copy_meets hCopy hw hsp (by omega) hsep)
    ?_ (by light_side [hn])
  rintro _ μ₂ ⟨hcopy, hsame⟩
  refine ⟨fun i hi => ?_, fun c hc => ?_⟩
  · rw [length_aeFlags] at hi
    change μ₂ (x.out + i) = _
    rw [hcopy i hi]
    exact hseg i (by rw [length_aeFlags]; exact hi)
  · exact (hsame c hc.2).trans (hkept c hc.1)

/-! ## The program -/

/-- The procedures of the all-edges host: the variant host's `et17Procs'` (numbers `o + 0` to
`o + 28`), then the all-edges scan of the pairs (29), the brute force (30), the loop (31), the core
(32), the top procedure (33) and `copy` (34). -/
def aeExtra (pS pD pG o : ℕ) : Program :=
  [scanPairsAEBody (o + 1),                                                   -- 29
    bruteAEBody (o + 1),                                                      -- 30
    hostLoopAEBody pS (o + 23) (o + 24) (o + 29) (o + 14),                    -- 31
    aeCoreBody (et17NumsAt pS pD pG o) (o + 30) (o + 31),                     -- 32
    aeTopBody (o + 32) (o + 34),                                              -- 33
    copyBody]                                                                 -- 34

@[inherit_doc aeExtra]
def aeProcs (pS pD pG o : ℕ) : Program := et17Procs' pS pD pG o ++ aeExtra pS pD pG o

/-- The number of the top procedure in `aeProcs`. -/
def iTop : ℕ := 33

variable {pS pD pG : ℕ}

/-- **The context of the all-edges host**, in the assembled program with anything appended. -/
theorem aeCtx_assembled (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) (R : Program) :
    AeCtx P₀ (aeProcs pS pD pG P₀.length ++ R) (et17NumsAt pS pD pG P₀.length)
      (P₀.length + 29) (P₀.length + 14) (P₀.length + 30) (P₀.length + 31) Tn need Dfun Gfun tD tG
      wD wG := by
  have L : ∀ {i : ℕ} {body : Stmt}, (aeProcs pS pD pG P₀.length)[i]? = some body →
      (P₀ ++ (aeProcs pS pD pG P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  have hbase := et17Ctx_assembled' hsol hD hG hpos (aeExtra pS pD pG P₀.length ++ R)
  rw [aeProcs, List.append_assoc]
  exact
    { base := hbase
      scanPairsAE := L (i := 29) rfl
      fill := L (i := 14) rfl
      bruteAE := L (i := 30) rfl
      loopAE := L (i := 31) rfl }

/-- **The all-edges host as a solver of all-edges Exact Triangle**: from a solver of
Lop-AE-SparseTri and two procedures that compute the parameters, in one program `P₀`, the appended
procedures make a solver of `aeTask` with the time `hostTimeAE` and the need `hostNeedAE`. -/
theorem ae17_solves (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) :
    Solves aeTask (P₀ ++ aeProcs pS pD pG P₀.length) (P₀.length + iTop)
      (hostTimeAE Dfun Gfun tD tG Tn) (hostNeedAE Dfun Gfun wD wG need) := by
  refine ⟨aeTopBody (P₀.length + 32) (P₀.length + 34), ?_, fun R lim d x μ fr hpre hok => ?_⟩
  · have htop := getElem?_append_append (P₀ := P₀) (B := aeProcs pS pD pG P₀.length) []
      (i := 33) rfl
    rwa [List.append_nil] at htop
  · rw [List.append_assoc]
    have C := aeCtx_assembled hsol hD hG hpos R
    exact aeTop_spec C (getElem?_append_append R (i := 32) rfl)
      (getElem?_append_append R (i := 34) rfl) x μ fr hpre hok

/-! ## The need stays polynomial -/

/-- **The need of the all-edges host stays polynomial**, if the parameters, the numbers that the
parameter procedures form, and the need of the solver are polynomially bounded. -/
theorem hostNeedAE_poly (hD : PolyBounded fun n _ => Dfun n)
    (hG : PolyBounded fun n _ => Gfun (Dfun n)) (hwD : PolyBounded fun n _ => wD n)
    (hwG : PolyBounded fun n _ => wG (Dfun n)) (h : PolyNeedN need) :
    PolyNeed (hostNeedAE Dfun Gfun wD wG need) := by
  obtain ⟨s, k, hle⟩ := hostNeed_poly' hD hG hwD hwG h
  refine ⟨1 + (s + 0), k + 2, fun n U => ?_⟩
  obtain ⟨hw, hc, hd⟩ := hle n U
  have hsq : n * n ≤ polyBound 0 2 [n, U] := by
    simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      pow_zero, one_mul]
    calc n * n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
      _ ≤ ((n + 1) * (U + 1)) * ((n + 1) * (U + 1)) := Nat.mul_le_mul
          (Nat.le_mul_of_pos_right _ (Nat.succ_pos U)) (Nat.le_mul_of_pos_right _ (Nat.succ_pos U))
      _ = ((n + 1) * (U + 1)) ^ 2 := (sq _).symm
  have hone : 1 ≤ polyBound 0 2 [n, U] := one_le_polyBound 0 2 [n, U]
  have hmono := polyBound_mono (Nat.le_add_right s 0 |>.trans (Nat.le_add_left _ 1))
    (Nat.le_add_right k 2) [n, U]
  refine ⟨hw.trans hmono, ?_, ?_⟩
  · exact add_le_polyBound hc hsq
  · exact (Nat.add_le_add hd hone).trans (add_le_polyBound le_rfl le_rfl)

/-! ## Over parameter routines -/

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean
/-- The all-edges host over two parameter routines, at the places `i` and `j` of a list `procs o`
of routines that stands behind a program of length `o`, turns a solver of Lop-AE-SparseTri into a
solver of all-edges Exact Triangle and keeps the need polynomial: the `host` hypothesis of
`claim17MidAE_of_host`. -/
theorem hostAE_of_paramProcs {procs : ℕ → Program} {i j : ℕ}
    (hD : ∀ Q R, ParamProc (Q ++ procs Q.length ++ R) (Q.length + i) Dfun tD wD)
    (hG : ∀ Q R, ParamProc (Q ++ procs Q.length ++ R) (Q.length + j) Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n)
    (hpoly : ∀ r, PolyNeedN r → PolyNeed (hostNeedAE Dfun Gfun wD wG r)) :
    ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves aeTask (Q ++ R) p' (hostTimeAE Dfun Gfun tD tG Tn)
        (hostNeedAE Dfun Gfun wD wG r) ∧ PolyNeed (hostNeedAE Dfun Gfun wD wG r) := by
  intro Q pS Tn r hr hs
  have h := ae17_solves (P₀ := Q ++ procs Q.length) (hs.append _) (hD Q) (hG Q) hpos
  rw [List.append_assoc] at h
  exact ⟨_, _, h, hpoly r hr⟩

end ImprovedExponents.AllEdges
