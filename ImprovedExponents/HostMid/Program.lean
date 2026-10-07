module

public import ImprovedExponents.HostMid.Correct

@[expose] public section

/-!
# The variant host: the program, assembled

The list `et17Procs'` of the procedures of the variant host is upstream's `et17Procs` with the top
procedure `et17Body'` in place of `et17Body`; the numbers of the procedures are upstream's
(`et17NumsAt`).  With a solver of Lop-AE-SparseTri and two parameter procedures it is a solver of
Exact Triangle with the time `hostTime'` and the need `hostNeed'` (`et17_solves'`).
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- The procedures of the variant host: procedure number `i` of this list gets the number `o + i`.
The top procedure `et17Body'` has the number `o + 27`; everything else is as in upstream's
`et17Procs`. -/
def et17Procs' (pS pD pG o : ℕ) : Program :=
  let ν := et17NumsAt pS pD pG o
  [sqrtBody,                                                -- 0
    scanBody,                                               -- 1
    bruteBody ν.pScan,                                      -- 2
    primesBody ν.ch.pSqrt ν.ch.pSieve,                      -- 3
    bitLenBody,                                             -- 4
    dblTableBody,                                           -- 5
    residBody,                                              -- 6
    residuesBody ν.pResid,                                  -- 7
    spreadTableBody,                                        -- 8
    szTableBody,                                            -- 9
    buildZBody,                                             -- 10
    countZeroBody,                                          -- 11
    vlinBody,                                               -- 12
    cconvBody,                                              -- 13
    fillBody,                                               -- 14
    phaseBody ν.ch.cp.str,                                  -- 15
    strBody ν.ch.cp.str,                                    -- 16
    countPrimeBody ν.ch.cp,                                 -- 17
    choosePrimeBody ν.ch,                                   -- 18
    queryCapNatBody,                                        -- 19
    ceilDivBody,                                            -- 20
    classesBody,                                            -- 21
    chunksBody,                                             -- 22
    writeXBody,                                             -- 23
    writeYBody,                                             -- 24
    scanPairsBody ν.pScan,                                  -- 25
    hostLoopBody pS ν.pWriteX ν.pWriteY ν.pScanPairs,       -- 26
    et17Body' ν,                                            -- 27
    sieveBody]                                              -- 28

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Program.lean
/-- **The context of the top procedure**, in the assembled program of the variant with anything
appended to it. -/
theorem et17Ctx_assembled' (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) (R : Program) :
    Et17Ctx P₀ (et17Procs' pS pD pG P₀.length ++ R) (et17NumsAt pS pD pG P₀.length) Tn need Dfun
      Gfun tD tG wD wG := by
  -- Procedure number `i` of the list.
  have L : ∀ {i : ℕ} {body : Stmt}, (et17Procs' pS pD pG P₀.length)[i]? = some body →
      (P₀ ++ (et17Procs' pS pD pG P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  exact
    { loop := ⟨hsol, L rfl, L rfl, L rfl, L rfl⟩
      hLoop := L rfl
      hSqrt := L (i := 0) rfl
      hBrute := L rfl
      hChoose := L rfl
      ch := ⟨L rfl, L rfl, L rfl,
        ⟨L rfl, L rfl, L rfl, L rfl, L rfl,
          L rfl, L rfl,
          ⟨L rfl, L rfl, L rfl, L rfl, L rfl⟩⟩,
        ⟨L (i := 0) rfl, L rfl⟩⟩
      hCap := L rfl
      hCeil := L rfl
      hBitLen := L rfl
      hDbl := L rfl
      hResid := L rfl
      hResidues := L rfl
      hClasses := L rfl
      hChunks := L rfl
      dProc := hD _
      gProc := hG _
      D_pos := hpos }

/-- **The variant host of Theorem 17 as a solver of Exact Triangle**: from a solver of
Lop-AE-SparseTri and two procedures that compute the parameters, in one program `P₀`, the appended
procedures make a solver of Exact Triangle with the time `hostTime'` and the need `hostNeed'`.  The
solver is called with the inner dimension `midSize D g`. -/
theorem et17_solves' (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) :
    Solves etTask (P₀ ++ et17Procs' pS pD pG P₀.length) (P₀.length + 27)
      (hostTime' Dfun Gfun tD tG Tn) (hostNeed' Dfun Gfun wD wG need) := by
  refine ⟨et17Body' (et17NumsAt pS pD pG P₀.length), ?_, fun R lim d x μ fr hpre hok => ?_⟩
  · have htop := getElem?_append_append (P₀ := P₀) (B := et17Procs' pS pD pG P₀.length) []
      (i := 27) rfl
    rwa [List.append_nil] at htop
  · rw [List.append_assoc]
    exact et17_spec' (et17Ctx_assembled' hsol hD hG hpos R) x μ fr hpre hok

end ImprovedExponents.HostMid
