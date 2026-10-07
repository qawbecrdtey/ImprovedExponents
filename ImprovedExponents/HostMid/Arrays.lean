module

public import ImprovedExponents.HostMid.PrimeStage

@[expose] public section

/-!
# The variant host: the arrays and the call of the loop

The third part of the host (the table of doubles, the residues, the classes, the chunks, and the
loop over the instances) has upstream's text `et17Tables`.  This file proves its specification for
the data `hostData'` of the variant, whose inner dimension is `midSize D g`: upstream's facts about
the third part are generic in the data, so only the two places that name the data of a run are
proved again (`ready_of'`, `et17Tables_spec'`).
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- What the third part needs holds for the data of a run of the variant. -/
theorem ready_of' {lim : Limits} {d : ℕ} {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ}
    {need : List ℕ → Need} {D g a b : ℕ} (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    Et17.Ready lim d x (hostData' x D g) μ fr := by
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok
  have hr := Et17.ready_of hpre hbig hok0
  have htop := aFr_le' (x := x) (g := g) hbig.sixteen_le fr
  have hcells := hok.cells
  simp only [hostNeedAt'] at hcells
  exact
    { space := hr.space
      depth := hr.depth
      prime := hr.prime
      word := hr.word
      top := by omega
      segAB := hr.segAB
      segBC := hr.segBC
      segAC := hr.segAC
      lenAB := hr.lenAB
      lenBC := hr.lenBC
      lenAC := hr.lenAC
      leAB := hr.leAB
      leBC := hr.leBC
      leAC := hr.leAC
      belowAB := hr.belowAB
      belowBC := hr.belowBC
      belowAC := hr.belowAC }

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Arrays.lean
open Et17 in
/-- **The third part of the variant**: the result of the loop over the instances; only cells from
the free pointer on change. -/
theorem et17Tables_spec' {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    {lim : Limits} {d : ℕ} (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Tables ν) ⟨frame (et17LocB' x fr D g), μ⟩
      (hostRunTime Tn (hostData' x D g) x.U)
      fun σ' => σ'.loc 0 = bit ((hostData' x D g).found (hostData' x D g).m) ∧
        Kept μ σ'.mem fr := by
  have hr := ready_of' hpre hbig hok
  have hlim := hostLim_of_ok' hbig hok
  have hv := hostData'_valid hpre hbig
  unfold et17LocB'
  generalize hostData' x D g = X at hr hlim hv ⊢
  have hdepth := hr.depth
  have hfr : fr ≤ aX X x.U fr := by
    have := host_places X x.U fr
    omega
  unfold et17Tables hostRunTime
  -- the table of doubles and the residues; the classes and the chunks
  refine resid_then C.hDbl C.hResid C.hResidues hr (fun r₁ μ₁ hresid => ?_) (by omega)
  refine classes_then C.hClasses C.hChunks hr hv.cap_pos hresid.rab
    (fun r₂ μ₂ hclass => ?_) (by omega)
  -- NumInst := NumPieces * NumChunks
  have hcount := hlim.count
  have hm : (X.m : ℤ) = (X.h : ℤ) * X.chunkCount := by
    rw [HostData.m]
    push_cast
    rfl
  have hpos : (0 : ℤ) ≤ (X.h : ℤ) * X.chunkCount := by positivity
  light_set (X.m : ℕ) using hm
  -- the result is pLoop(…)
  light_call (Meets.of_body (Q := fun r μ' => r = bit (X.found X.m) ∧
      Kept μ₂ μ' (hostAddr x X fr).x) C.hLoop
    (hostLoop_spec C.loop ⟨hv, hr.leAB, hr.leBC, hr.leAC⟩ (hostMem_of hr hresid hclass)
      (hostLay_of hr (hr.chunkCount_le hv.cap_pos)) hlim)) using hostLoopArgs, hostAddr
    with r μ₃ ⟨rfl, hkept⟩
  refine ⟨rfl, fun c hc => ?_⟩
  have hcls : fr ≤ aCls X x.U fr := by
    have := host_places X x.U fr
    omega
  exact (hkept c (lt_of_lt_of_le hc hfr)).trans ((hclass.same c (Or.inl (by omega))).trans
    (hresid.same c (Or.inl hc)))

end ImprovedExponents.HostMid
