module

public import ThreeSumApsp.Programs.Sec3.Theorem17.ClaimAtParameters

@[expose] public section

/-!
# The host of Theorem 17 with a smaller inner dimension: the program, its time and its need

Upstream's host `et17` (Exact Triangle by Theorem 17) hands the parameter `D` to the solver of
Lop-AE-SparseTri as the inner dimension of every instance.  The middle part of an instance is
`piece × ℤ_p` with at most `q = ⌈⌊√D⌋/g⌉` vertices in the piece and a prime `p ≤ ⌊√D⌋`, so only
the first `q ⌊√D⌋` columns of the matrices are used.  The variant `et17Body'` of this directory
hands the solver the inner dimension `midSize D g = q ⌊√D⌋` instead.  The text differs from
upstream's in one assignment (`et17Sizes'`): after the prime, the cap and the size of a piece are
computed from `D`, the local `ParD` is overwritten with `q ⌊√D⌋`.

This file holds the changed text, the data of a run (`hostData'`), and the time and the need of the
variant (`hostTime'`, `hostNeed'`).  They are upstream's time and need over a solver whose
parameters are rewritten by `midArgs` (`hostTime'_eq`, `hostNeed'_eq`).
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-! ## The inner dimension -/

/-- The inner dimension that the variant host hands to the solver: `⌈⌊√D⌋/g⌉ ⌊√D⌋`, the number of
vertices of a piece times the largest possible prime. -/
def midSize (D g : ℕ) : ℕ := pieceSizeNat D g * Nat.sqrt D

/-- A piece has at most `⌊√D⌋` vertices, for every `g`. -/
theorem pieceSizeNat_le_sqrt (D g : ℕ) : pieceSizeNat D g ≤ Nat.sqrt D := by
  unfold pieceSizeNat
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  · exact (ceilDiv_le_iff_le_smul hg).2 (by simpa using Nat.le_mul_of_pos_left _ hg)

/-- The inner dimension of the variant is at most `D`, for every `g`. -/
theorem midSize_le (D g : ℕ) : midSize D g ≤ D :=
  (Nat.mul_le_mul_right _ (pieceSizeNat_le_sqrt D g)).trans (Nat.sqrt_le D)

/-- The inner dimension of the variant is positive under the hypotheses of Theorem 17. -/
theorem one_le_midSize {D g : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g) : 1 ≤ midSize D g := by
  have hsqrt : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
  have hpiece : 1 ≤ pieceSizeNat D g := (Nat.lt_ceilDiv_iff hg).2 (by omega)
  exact Nat.mul_pos hpiece (by omega)

/-- The parameters `[n, D, w]` of an instance of upstream's host, rewritten to those of the
variant: `[n, midSize D (G D), w]`, where `G` computes `g` from `D`. -/
def midArgs (G : ℕ → ℕ) : List ℕ → List ℕ
  | [n, D, w] => [n, midSize D (G D), w]
  | ps => ps

/-- Rewriting the parameters does not increase a polynomial bound. -/
theorem polyBound_midArgs_le (G : ℕ → ℕ) (s k : ℕ) (ps : List ℕ) :
    polyBound s k (midArgs G ps) ≤ polyBound s k ps := by
  unfold midArgs
  split
  · simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    gcongr
    exact midSize_le _ _
  · exact le_rfl

/-- A polynomially bounded need stays so when the parameters are rewritten. -/
theorem polyNeedN_midArgs {need : List ℕ → Need} (G : ℕ → ℕ) (h : PolyNeedN need) :
    PolyNeedN fun ps => need (midArgs G ps) := by
  obtain ⟨s, k, hle⟩ := h
  exact ⟨s, k, fun ps => ⟨(hle _).1.trans (polyBound_midArgs_le G s k ps),
    (hle _).2.1.trans (polyBound_midArgs_le G s k ps),
    (hle _).2.2.trans (polyBound_midArgs_le G s k ps)⟩⟩

/-! ## The procedure -/

open Et17 in
/-- The second part of the variant: the prime, the sizes, then `ParD := PieceLen * RootD`, and the
addresses of the arrays.  Upstream's `et17Sizes` with one more assignment. -/
def et17Sizes' (ν : Et17Nums) : Stmt :=
  .call ν.pChoose [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v ParD, v Free] ThePrime ;;
  .call ν.pCap [v Size, v ParD] Cap ;;
  .call ν.pCeil [v RootD, v ParG] PieceLen ;;
  .call ν.pCeil [v Size, v PieceLen] NumPieces ;;
  .call ν.pBitLen [v Bound] Bits ;;
  .set ParD (v PieceLen *' v RootD) ;;
  et17Addr

open Et17 in
/-- The variant of et17(n, U, ab, bc, ac, fr): upstream's `et17Body` with `et17Sizes'`. -/
def et17Body' (ν : Et17Nums) : Stmt :=
  et17Params ν ;;
  .ite (v Small =' k 1)
    (.call ν.pBrute [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free] 0)
    (et17Sizes' ν ;; et17Tables ν)

/-! ## Time and need -/

/-- A bound on the time of the loop over the instances of the variant: as upstream's
`hostLoopBound`, with the solver at the inner dimension `midSize D g`. -/
noncomputable def hostLoopBound' (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  4 * n * g *
      (tWrites n D (pieceSizeNat D g) + supTime Tn n (midSize D g) (queryCapNat n D)
        + tAnswers (queryCapNat n D))
    + tScanCall (pieceSizeNat D g) * (falsePositiveBound n U D + 1) + 14

/-- The time of the variant after the tests, if n is not small. -/
noncomputable def hostMain' (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  chooseTime n U D + tQueryCapNat n D + tCeilDiv (Nat.sqrt D) g + tCeilDiv n (pieceSizeNat D g)
    + tBitLen U + tDblTable (bitLen U) + 3 * tResidues (n * n) (bitLen U) + tClasses n (Nat.sqrt D)
    + tChunks (Nat.sqrt D) (4 * n * g) + hostLoopBound' Tn n U D g + 300

/-- **A bound on the time of the variant host in the worst case**, for the parameter functions
Dfun, Gfun with the times tD, tG, over a solver with the time Tn. -/
noncomputable def hostTime' (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostSetup tD tG n (Dfun n) +
    if SmallCase n (Dfun n) (Gfun (Dfun n)) then tBrute n + 20
    else hostMain' Tn n U (Dfun n) (Gfun (Dfun n))

/-- The need of the variant host for given parameters D and g: as upstream's `hostNeedAt`, with the
solver at the inner dimension `midSize D g`. -/
def hostNeedAt' (a b : ℕ) (need : List ℕ → Need) (n U D g : ℕ) : Need :=
  ⟨hostWord a b n U D g + (supNeed need n (midSize D g) (queryCapNat n D)).word,
    chooseCells n U D + hostLayout n U D + (supNeed need n (midSize D g) (queryCapNat n D)).cells
      + 2,
    2 * Nat.clog 2 n + 8 + (supNeed need n (midSize D g) (queryCapNat n D)).depth⟩

/-- **The need of the variant host**, over a solver with the need `need`; wD and wG bound the
numbers that the parameter procedures form. -/
def hostNeed' (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  hostNeedAt' (wD n) (wG (Dfun n)) need n U (Dfun n) (Gfun (Dfun n))

/-- The time of the variant is upstream's time over a solver with rewritten parameters. -/
theorem hostTime'_eq (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) :
    hostTime' Dfun Gfun tD tG Tn n U
      = hostTime Dfun Gfun tD tG (fun ps => Tn (midArgs Gfun ps)) n U :=
  rfl

/-- The need of the variant for given parameters is upstream's need over a solver with rewritten
parameters. -/
theorem hostNeedAt'_eq (a b : ℕ) (need : List ℕ → Need) (n U D g : ℕ) :
    hostNeedAt' a b need n U D g
      = hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) n U D g :=
  rfl

/-- The need of the variant is upstream's need over a solver with rewritten parameters. -/
theorem hostNeed'_eq (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) :
    hostNeed' Dfun Gfun wD wG need n U
      = hostNeed Dfun Gfun wD wG (fun ps => need (midArgs Gfun ps)) n U :=
  rfl

/-! ## The data and the local variables of a run -/

/-- The data of the loop over the instances of the variant, for the parameters D and g: upstream's
`hostData` with the inner dimension `midSize D g`. -/
def hostData' (x : TriInst) (D g : ℕ) : HostData :=
  ⟨x.n, midSize D g, chosenPrime x.n D x.AB x.BC x.AC, pieceSizeNat D g, queryCapNat x.n D, x.AB,
    x.BC, x.AC⟩

/-- The locals after the second part of the variant (n is not small, so the flag is 0). -/
def et17LocB' (x : TriInst) (fr D g : ℕ) : List ℤ :=
  Et17.locals x (hostData' x D g) fr g (Nat.sqrt D : ℕ) 0 0

end ImprovedExponents.HostMid
