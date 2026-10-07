module

public import ImprovedExponents.AllEdges.Host.LoopAE
public import ImprovedExponents.AllEdges.Host.BruteAE
public import ImprovedExponents.HostMid.Correct

@[expose] public section

/-!
# The all-edges host: the program, its time and its need

The all-edges variant of the host of Theorem 17 is the host of `ImprovedExponents.HostMid` (the
solver is charged at the inner dimension `midSize D g`) with the loop over the instances replaced
by `hostLoopAE`, the brute force by `bruteAE`, and the solver's free pointer moved up by `n²` cells
that hold the flags (`et17TablesAE`, `aeCoreBody`).  The top procedure `aeTopBody` copies the `n²`
flags to the place `out` of the task (`aeTask`).

This file holds the text, the time (`hostTimeAE`), the need (`hostNeedAE`), the specifications of
the parts (`et17TablesAE_spec`, `aeCore_spec`, `aeTop_spec`), the assembled program (`aeProcs`)
and the statement that it solves all-edges Exact Triangle (`ae17_solves`).
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec HostMid

/-! ## The text -/

open Et17 in
/-- The third part of the all-edges host: upstream's `et17Tables` with the all-edges loop, whose
free pointer is `n²` cells above the answers; the flags lie in between. -/
def et17TablesAE (ν : Et17Nums) (pLoopAE : ℕ) : Stmt :=
  .call ν.pDbl [v Free, v ThePrime, v Bits] Small ;;
  .call ν.pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols] Small ;;
  .call ν.pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks ;;
  .set NumInst (v NumPieces *' v NumChunks) ;;
  .call pLoopAE [v Size, v ParD, v ThePrime, v PieceLen, v NumChunks, v NumInst, v AdrAB, v AdrBC,
    v AdrAC, v ResAC, v ResBC, v Rows, v Cols, v TabR, v TabL, v TabW, v MatX, v MatY, v AdrOut,
    v SolverFree +' v SizeSq] 0

open Et17 in
/-- aeCore(n, U, ab, bc, ac, fr): the parameters, then the brute force or the three parts of the
variant host; it returns the address of the `n²` flags, which lie at or above `fr`. -/
def aeCoreBody (ν : Et17Nums) (pBruteAE pLoopAE : ℕ) : Stmt :=
  et17Params ν ;;
  .ite (v Small =' k 1)
    (.call pBruteAE [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free] 0)
    (et17Sizes' ν ;; et17TablesAE ν pLoopAE)

/-- ae(n, U, ab, bc, ac, out, fr): the core, then the `n²` flags are copied to `out`. -/
def aeTopBody (pCore pCopy : ℕ) : Stmt :=
  .call pCore [v 0, v 1, v 2, v 3, v 4, v 6] 7 ;;
  .call pCopy [v 7, v 5, v 0 *' v 0] 7

/-! ## Time and need -/

/-- A bound on the time of the all-edges loop: as `hostLoopBound'`, with the all-edges scan of the
answers, at most `falsePositiveBound + n²` scans, and the filling of the flags. -/
noncomputable def hostLoopBoundAE (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  4 * n * g *
      (tWrites n D (pieceSizeNat D g) + supTime Tn n (midSize D g) (queryCapNat n D)
        + tAnswersAE (queryCapNat n D))
    + tScanCallAE (pieceSizeNat D g) * (falsePositiveBound n U D + n * n) + fillTime (n * n) + 40

/-- The time of the core after the tests, if n is not small. -/
noncomputable def hostMainAE (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  chooseTime n U D + tQueryCapNat n D + tCeilDiv (Nat.sqrt D) g + tCeilDiv n (pieceSizeNat D g)
    + tBitLen U + tDblTable (bitLen U) + 3 * tResidues (n * n) (bitLen U) + tClasses n (Nat.sqrt D)
    + tChunks (Nat.sqrt D) (4 * n * g) + hostLoopBoundAE Tn n U D g + 300

/-- A bound on the time of the core in the worst case. -/
noncomputable def hostCoreTime (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostSetup tD tG n (Dfun n) +
    if SmallCase n (Dfun n) (Gfun (Dfun n)) then tBruteAE n + 20
    else hostMainAE Tn n U (Dfun n) (Gfun (Dfun n))

/-- **A bound on the time of the all-edges host in the worst case**, for the parameter functions
Dfun, Gfun with the times tD, tG, over a solver with the time Tn: the core and the copy. -/
noncomputable def hostTimeAE (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostCoreTime Dfun Gfun tD tG Tn n U + copyTime (n * n) + 20

/-- The need of the core of the all-edges host for given parameters D and g: `hostNeedAt'` with
`n²` more cells for the flags. -/
def hostNeedCoreAt (a b : ℕ) (need : List ℕ → Need) (n U D g : ℕ) : Need :=
  ⟨(hostNeedAt' a b need n U D g).word, (hostNeedAt' a b need n U D g).cells + n * n,
    (hostNeedAt' a b need n U D g).depth⟩

/-- The need of the core of the all-edges host. -/
def hostNeedCore (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  hostNeedCoreAt (wD n) (wG (Dfun n)) need n U (Dfun n) (Gfun (Dfun n))

/-- **The need of the all-edges host**, over a solver with the need `need`: that of the core, one
level of calls up. -/
def hostNeedAE (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  ⟨(hostNeedCore Dfun Gfun wD wG need n U).word, (hostNeedCore Dfun Gfun wD wG need n U).cells,
    (hostNeedCore Dfun Gfun wD wG need n U).depth + 1⟩

/-- The need of the variant host is allowed for when that of the all-edges host is. -/
theorem hostNeedAt'_ok {lim : Limits} {d a b n U D g : ℕ} {need : List ℕ → Need} {fr : ℕ}
    (hok : (hostNeedCoreAt a b need n U D g).Ok lim fr d) :
    (hostNeedAt' a b need n U D g).Ok lim fr d :=
  hok.mono le_rfl (by simp only [hostNeedCoreAt]; omega) (by simp only [hostNeedCoreAt]; omega)

/-- The time of the third part in a run of the all-edges host. -/
def hostRunTimeAE (Tn : List ℕ → ℕ) (X : HostData) (U : ℕ) : ℕ :=
  tDblTable (bitLen U) + 3 * tResidues (X.n * X.n) (bitLen U) + tClasses X.n X.p
    + tChunks X.p X.chunkCount + tHostLoopAE Tn X + 80

/-! ## The context -/

/-- The context of the all-edges host: that of the variant host, and the new procedures. -/
structure AeCtx (P₀ R : Program) (ν : Et17Nums) (pScanPairsAE pFill pBruteAE pLoopAE : ℕ)
    (Tn : List ℕ → ℕ) (need : List ℕ → Need) (Dfun Gfun tD tG wD wG : ℕ → ℕ) : Prop where
  base : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG
  scanPairsAE : (P₀ ++ R)[pScanPairsAE]? = some (scanPairsAEBody ν.pScan)
  fill : (P₀ ++ R)[pFill]? = some fillBody
  bruteAE : (P₀ ++ R)[pBruteAE]? = some (bruteAEBody ν.pScan)
  loopAE : (P₀ ++ R)[pLoopAE]? =
    some (hostLoopAEBody ν.pS ν.pWriteX ν.pWriteY pScanPairsAE pFill)

variable {P₀ R : Program} {ν : Et17Nums} {pScanPairsAE pFill pBruteAE pLoopAE : ℕ}
  {Tn : List ℕ → ℕ} {need : List ℕ → Need} {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

/-- The context of the all-edges loop. -/
theorem AeCtx.loop (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG
    wD wG) :
    HostCtxAE P₀ R ν.pS ν.pWriteX ν.pWriteY ν.pScanPairs ν.pScan pScanPairsAE pFill Tn need :=
  { C.base.loop with scanPairsAE := C.scanPairsAE, fill := C.fill }

/-! ## The third part -/

/-- The addresses of the all-edges loop: upstream's, with the free pointer `n²` cells up. -/
def hostAddrAE (x : TriInst) (X : HostData) (fr : ℕ) : HostAddr :=
  { hostAddr x X fr with fr := aFr X x.U fr + X.n * X.n }

/-- What the all-edges loop asks of the limits. -/
theorem hostLimAE_of_ok {a b : ℕ} {x : TriInst} {fr D g : ℕ} (hbig : BigCase x.n D g)
    (hok : (hostNeedCoreAt a b need x.n x.U D g).Ok lim fr d) :
    HostLim lim (d + 1) (hostData' x D g) x.U (hostAddrAE x (hostData' x D g) fr) need := by
  have h := hostLim_of_ok' hbig (hostNeedAt'_ok hok)
  have hcells := hok.cells
  have hfr := aFr_le' (x := x) (g := g) hbig.sixteen_le fr
  simp only [hostNeedCoreAt, hostNeedAt'] at hcells
  exact
    { space := h.space
      fr := by change aFr (hostData' x D g) x.U fr + x.n * x.n < lim.space; omega
      prime := h.prime
      count := h.count
      step := h.step
      weights := h.weights
      depth := by have := hok.depth; simp only [hostNeedCoreAt, hostNeedAt'] at this; omega
      solver := fun t ht => by
        have hs := h.solver t ht
        have hwc : (hostData' x D g).w t ≤ queryCapNat x.n D := (hostData' x D g).w_le_cap ht
        have hscells :
            (need [(hostData' x D g).n, (hostData' x D g).D, (hostData' x D g).w t]).cells
              ≤ (supNeed need x.n (midSize D g) (queryCapNat x.n D)).cells :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).cells)
            (Finset.mem_range.2 (by omega))
        exact ⟨hs.word, by change aFr (hostData' x D g) x.U fr + x.n * x.n + _ ≤ _; omega,
          hs.space, hs.depth⟩ }

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Arrays.lean
open Et17 in
/-- **The third part of the all-edges host**: the result is the address of the flags, which hold
the flags of all-edges Exact Triangle; only cells from the free pointer on change. -/
theorem et17TablesAE_spec
    (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedCoreAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17TablesAE ν pLoopAE) ⟨frame (et17LocB' x fr D g), μ⟩
      (hostRunTimeAE Tn (hostData' x D g) x.U)
      fun σ' => ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧ σ'.loc 0 = flg ∧
        Seg σ'.mem flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ σ'.mem fr := by
  have hok' := hostNeedAt'_ok hok
  have hr := ready_of' hpre hbig hok'
  have hlim := hostLimAE_of_ok hbig hok
  have hv := hostData'_valid hpre hbig
  have hdepth := hok.depth
  simp only [hostNeedCoreAt, hostNeedAt'] at hdepth
  unfold et17LocB'
  generalize hX : hostData' x D g = X at hr hlim hv ⊢
  have hn : X.n = x.n := by rw [← hX]; rfl
  have hfr : fr ≤ aX X x.U fr := by
    have := host_places X x.U fr
    omega
  unfold et17TablesAE hostRunTimeAE
  -- the table of doubles and the residues; the classes and the chunks
  refine resid_then C.base.hDbl C.base.hResid C.base.hResidues hr (fun r₁ μ₁ hresid => ?_)
    (by omega)
  refine classes_then C.base.hClasses C.base.hChunks hr hv.cap_pos hresid.rab
    (fun r₂ μ₂ hclass => ?_) (by omega)
  -- NumInst := NumPieces * NumChunks
  have hcount := hlim.count
  have hm : (X.m : ℤ) = (X.h : ℤ) * X.chunkCount := by
    rw [HostData.m]
    push_cast
    rfl
  have hpos : (0 : ℤ) ≤ (X.h : ℤ) * X.chunkCount := by positivity
  light_set (X.m : ℕ) using hm
  -- the result is pLoopAE(…)
  have hlay := hostLay_of hr (hr.chunkCount_le hv.cap_pos)
  have hplaces := host_places X x.U fr
  have hx : aX X x.U fr ≤ aFr X x.U fr := by omega
  have hfrA : (hostAddr x X fr).fr = aFr X x.U fr := rfl
  have hfrS : aFr X x.U fr + X.n * X.n < lim.space := hlim.fr
  have hsw := hlim.space
  have hfrW : (aFr X x.U fr : ℤ) + (X.n : ℤ) * (X.n : ℤ) ≤ lim.word := by
    have : ((aFr X x.U fr + X.n * X.n : ℕ) : ℤ) ≤ lim.word := by
      exact_mod_cast (Nat.cast_lt.2 hfrS).le.trans hsw
    push_cast at this
    exact this
  have houtA : (hostAddr x X fr).out = aOut X x.U fr := rfl
  have hF : FlagsPlace X (hostAddrAE x X fr) (aFr X x.U fr) := ⟨rfl, hx, hlay.ofr⟩
  have hofr : ∀ t < X.m, (hostAddrAE x X fr).out + X.w t ≤ (hostAddrAE x X fr).fr := fun t ht => by
    have := hlay.ofr t ht
    change (hostAddr x X fr).out + X.w t ≤ aFr X x.U fr + X.n * X.n
    omega
  have hlay' : HostLay X (hostAddrAE x X fr) := { hlay with ofr := hofr }
  have hargs : ((aFr X x.U fr + X.n * X.n : ℕ) : ℤ) = (aFr X x.U fr : ℤ) + ((X.n * X.n : ℕ) : ℤ) :=
    by push_cast; rfl
  light_call (Meets.of_body (Q := fun r μ' => r = aFr X x.U fr ∧
      Seg μ' (aFr X x.U fr) (aeFlags X.n X.AB X.BC X.AC) ∧ Kept μ₂ μ' (hostAddrAE x X fr).x)
    C.loopAE (hostLoopAE_spec C.loop ⟨hv, hr.leAB, hr.leBC, hr.leAC⟩
      { hostMem_of hr hresid hclass with } hlay' hlim hF)) using hostLoopArgs, hostAddrAE, hostAddr,
    hargs with r μ₃ ⟨rfl, hflags, hkept⟩
  refine ⟨aFr X x.U fr, by omega, by rw [← hn]; omega, rfl, ?_, fun c hc => ?_⟩
  · have hAB : X.AB = x.AB := by rw [← hX]; rfl
    have hBC : X.BC = x.BC := by rw [← hX]; rfl
    have hAC : X.AC = x.AC := by rw [← hX]; rfl
    rwa [hn, hAB, hBC, hAC] at hflags
  · have hcls : fr ≤ aCls X x.U fr := by omega
    exact (hkept c (lt_of_lt_of_le hc hfr)).trans ((hclass.same c (Or.inl (by omega))).trans
      (hresid.same c (Or.inl hc)))

/-! ## The time of a run is within the worst case -/

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Time.lean
/-- The time of an instance of the all-edges host with a piece of `len ≤ q` vertices, `w ≤ cap`
query pairs and `execs` scans is at most the worst case for `q` and `cap` plus the time of the
scans. -/
theorem instanceAE_le (Tn : List ℕ → ℕ) (n D g execs : ℕ) {len q w cap : ℕ} (hlen : len ≤ q)
    (hw : w ≤ cap) :
    tWrites n (midSize D g) len + Tn [n, midSize D g, w] + tScanPairsAE w len execs
      ≤ tWrites n D q + supTime Tn n (midSize D g) cap + tAnswersAE cap
        + tScanCallAE q * execs := by
  have hwrites := tWrites_le n (midSize_le D g) hlen
  have hsolver : Tn [n, midSize D g, w] ≤ supTime Tn n (midSize D g) cap :=
    Finset.le_sup (f := fun w => Tn [n, midSize D g, w]) (Finset.mem_range.2 (by omega))
  have hanswers : tAnswersAE w ≤ tAnswersAE cap := by
    unfold tAnswersAE
    gcongr
  have hscans : tScanCallAE len * execs ≤ tScanCallAE q * execs := by
    unfold tScanCallAE tScan
    gcongr
  unfold tScanPairsAE
  omega

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

/-- Each scan fails or sets a flag: at most `falsePositiveBound + n²` scans. -/
theorem sum_execsAE_le_falsePositiveBound (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) :
    ∑ t ∈ Finset.range (hostData' x D g).m, (hostData' x D g).execsAE t
      ≤ falsePositiveBound x.n x.U D + x.n * x.n :=
  ((hostData' x D g).sum_execsAE_le (hostData'_valid hpre hbig)).trans (Nat.add_le_add_right
    ((HostData.sum_fails_le (hostData'_valid hpre hbig)).trans (F_le_falsePositiveBound hpre hbig))
    _)

/-- The time of the all-edges loop is within its bound. -/
theorem tHostLoopAE_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    tHostLoopAE Tn (hostData' x D g) ≤ hostLoopBoundAE Tn x.n x.U D g := by
  unfold tHostLoopAE hostLoopBoundAE
  exact Nat.add_le_add_right (Nat.add_le_add_right (sum_le_mul_add
    (fun _ ht => instanceAE_le Tn x.n D g _ (Nat.min_le_left _ _) ((hostData' x D g).w_le_cap ht))
    (hostData'_m_le hbig) (sum_execsAE_le_falsePositiveBound hpre hbig)) _) _

/-- **The time of a run of the all-edges host after the choice of the prime is within the worst
case.** -/
theorem hostRunTimeAE_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    hostRunTimeAE Tn (hostData' x D g) x.U
      ≤ tDblTable (bitLen x.U) + 3 * tResidues (x.n * x.n) (bitLen x.U)
        + tClasses x.n (Nat.sqrt D) + tChunks (Nat.sqrt D) (4 * x.n * g)
        + hostLoopBoundAE Tn x.n x.U D g + 80 := by
  have hprime : (hostData' x D g).p ≤ Nat.sqrt D := hostData'_p_le x g hbig.sixteen_le
  have hchunks : (hostData' x D g).chunkCount ≤ 4 * x.n * g :=
    (chunkCount_le_m (hostData'_valid hpre hbig)).trans (hostData'_m_le hbig)
  have hloop := tHostLoopAE_le hpre hbig Tn
  have hn : (hostData' x D g).n = x.n := rfl
  unfold hostRunTimeAE
  rw [hn]
  unfold tClasses tChunks
  omega

end ImprovedExponents.AllEdges
