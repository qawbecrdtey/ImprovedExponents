module

public import ImprovedExponents.HostMid.Need

@[expose] public section

/-!
# The variant host: the prime, the sizes, the new inner dimension, the addresses

This file proves the specification of the second part `et17Sizes'` of the variant host: upstream's
five calls, the assignment `ParD := PieceLen * RootD` that makes `midSize D g` the inner dimension,
and upstream's seventeen assignments of the addresses (`et17Addr_spec`, which is generic in the
data).  The time is that of upstream's second part: its constant covers the additional assignment.
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/PrimeStage.lean
/-- **The second part of the variant**: the prime, the sizes and the addresses are in the locals,
and `ParD` holds `midSize D g`; only cells from the free pointer on have changed. -/
theorem et17Sizes_spec' {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Sizes' ν) ⟨frame (et17LocA x fr D g), μ⟩
      (chooseTime x.n x.U D + tQueryCapNat x.n D + tCeilDiv (Nat.sqrt D) g +
        tCeilDiv x.n (pieceSizeNat D g) + tBitLen x.U + 120)
      fun σ' => ∃ μ', σ' = ⟨frame (et17LocB' x fr D g), μ'⟩ ∧ Kept μ μ' fr := by
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok
  have hr := sizesReady_of (x := x) hbig hok0
  have hdepth := hr.depth
  have htop : aFr (hostData' x D g) x.U fr ≤ lim.space := by
    have hfr := aFr_le' (x := x) (g := g) hbig.sixteen_le fr
    have hcells := hok.cells
    simp only [hostNeedAt'] at hcells
    omega
  -- The new inner dimension is at most `D`, so it fits in a word.
  have hmid : ((midSize D g : ℕ) : ℤ) = ((Nat.sqrt D ⌈/⌉ g : ℕ) : ℤ) * (Nat.sqrt D : ℤ) := by
    unfold midSize pieceSizeNat
    push_cast
    rfl
  have hmidWord : ((midSize D g : ℕ) : ℤ) ≤ lim.word :=
    le_word_of_le_hostWord hok0 ((midSize_le D g).trans (by unfold hostWord; omega))
  unfold et17Sizes' et17LocA
  rw [ite_eq_right (not_smallCase_iff.2 hbig)]
  -- ThePrime := pChoose(Size, Bound, AdrAB, AdrBC, AdrAC, ParD, Free)
  light_call (choosePrime_meets C.hChoose C.ch (choosePre_of_ok hpre hok0)) with _ μ₁ ⟨rfl, hμ₁⟩
  -- Cap := pCap(Size, ParD)
  light_call (queryCapNat_meets C.hCap hr.one_le_D hr.wordCap) with _ μ₁ ⟨rfl, rfl⟩
  -- PieceLen := pCeil(RootD, ParG)
  light_call (ceilDiv_meets C.hCeil hr.one_le_g hr.wordPiece) with _ μ₁ ⟨rfl, rfl⟩
  -- NumPieces := pCeil(Size, PieceLen)
  light_call (ceilDiv_meets C.hCeil hr.one_le_piece hr.wordPieces) using pieceSizeNat
    with _ μ₁ ⟨rfl, rfl⟩
  -- Bits := pBitLen(Bound)
  light_call (bitLen_meets C.hBitLen hr.wordBits) with _ μ₁ ⟨rfl, rfl⟩
  -- ParD := PieceLen * RootD
  light_set (midSize D g : ℕ) using hmid
  -- the sizes and the addresses
  refine (et17Addr_spec x (hostData' x D g) hok.space htop).mono (by simp [et17Addr]; omega) ?_
  rintro _ rfl
  exact ⟨μ₁, rfl, fun c hc => hμ₁ c (Or.inl hc)⟩

end ImprovedExponents.HostMid
