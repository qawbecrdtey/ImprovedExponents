module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.AllBands
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract
public import ImprovedExponents.PrunedProgram.Encode.Meaning
public import ImprovedExponents.PrunedProgram.Procs
import all ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract

@[expose] public section

/-!
# The encodings of all bands of one matrix with the pruned encoder

Upstream's `encodeBands` (`ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean`) calls, for
each band `β`, `bandArray` and then `encode`, which leaves the full encoding of the band in the
`T = 10^L` cells from `enc + β T`.  `encodeBandsP` is the same loop with the pruned encoder
`encodeP` in place of `encode`, called with the budget `m` (the inner size): the encodings are right
at the leaves with at most `m` symbols `P₀` (`SegOn p.m`), and the time has the work
`encWorkP p.L p.m` of the pruned encoder in place of `p.T`.  The loop is treated once, for callees
described by what they do here (`encodeBandsP_proc`); the two entries put in upstream's
specification of `bandArray` and the specification of `encodeP` (`encodeP_entry`, the analogue of
upstream's `encode_entry` in `Encode/Contract.lean`).

Adapted from upstream `ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean` and
`Encode/Contract.lean` (Apache-2.0).
-/

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents

variable {lim : Limits} {P : Program}

open private scrSize_le pow_of_seg from ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract

/-! ## The specification of the pruned encoder that its callers assume -/

variable {n Lmax j src dst scr tab p7 p10 : ℕ} {μ : ℕ → ℤ}

/-- **The specification that the callers of encodeP assume**, for any alphabet of seven variables.
The callers allow `7^n` cells of scratch area, more than the `scrSize n` that `encodeP` uses. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Contract.lean (encode_entry)
theorem encodeP_entry {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)
    {T : List ℤ} (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) (std : Std lim)
    (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {d : ℕ} (hd : d + (n + 1) ≤ lim.depth) (hpl : EncodePlaces lim n Lmax src dst scr tab p7 p10 μ)
    (htab : Seg μ tab T) (A : (Fin n → α) → ℤ) (hsrc : Seg μ src (arrStr e A)) {V : ℤ}
    (hV : ∀ u, |A u| ≤ V) (hVB : 7 ^ (n + 1) * V ≤ lim.word) (hj : (j : ℤ) ≤ lim.word) :
    Meets lim P Proc.encodeP d [n, j, src, dst, scr, tab, p7, p10] μ (cEncP * encWorkP n j)
      fun _ μ' => SegOn j μ' dst (computeEncoding coef n A) ∧
        SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n) := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV fun _ => e.symm 0)
  have hVB' : ((7 ^ n : ℕ) : ℤ) * V ≤ lim.word := by
    refine le_trans ?_ hVB
    push_cast
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)) hV0
  have hscr := scrSize_le n
  refine .of_body hE ((encodeP_str e coef hT hc hcoef hS hE (hpl.layout std) A hsrc hV htab
    (pow_of_seg hpl.hp7 hpl.n_le) (pow_of_seg hpl.hp10 hpl.n_le) hVB' (by omega) hj).mono le_rfl
    fun σ' h => ⟨h.1, h.2.mono fun x hx => by omega⟩)

/-! ## The loop -/

open Bands in
/-- encodeBandsP(L, m, N, D, K0, N0, S7, T, nB, side, aA, sI, sK, mask, dig3, dig4, arr, zs, tab,
p7, p10, enc): for each band, the input array is formed at arr and encoded with the budget m into
the T cells from enc + β T. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (encodeBandsBody)
def encodeBandsPBody : Stmt :=
  .for BandNo (v NumBands) (
    .call pBandArray [v Levels, v Size, v Rows, v Cols, v NumBlocks, v Width, v Cells, v BandNo,
      v Side, v Source, v StepRow, v StepCol, v MaskTable, v Digits3, v Digits4, v Arr] Res ;;
    .call Proc.encodeP [v Levels, v Size, v Arr, v Enc +' v BandNo *' v Leaves, v Scratch, v Table,
      v Pow7, v Pow10] Res)

/-- The time of the loop is at most the constant cB + cE + 51 times the shape of the entries. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (encodeBands_time)
theorem encodeBandsP_time (p : Par) (cB cE : ℕ) :
    p.nB * (cB * bandArrayShape p + cE * encWorkP p.L p.m + 51) + 6
      ≤ (cB + cE + 51) * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1) := by
  have hW : 1 ≤ encWorkP p.L p.m :=
    (Nat.one_le_pow _ _ (by norm_num)).trans (pow_seven_le_encWorkP p.L p.m)
  have hfifty : p.nB * 51 ≤ p.nB * (51 * encWorkP p.L p.m) := Nat.mul_le_mul_left _ (by omega)
  generalize encWorkP p.L p.m = W at hW hfifty ⊢
  calc p.nB * (cB * bandArrayShape p + cE * W + 51) + 6
      = p.nB * (cB * bandArrayShape p) + p.nB * (cE * W) + p.nB * 51 + 6 := by ring
    _ ≤ p.nB * (cB * bandArrayShape p) + p.nB * (cE * W) + p.nB * (51 * W) + 6
        + (p.nB * (cB * W) + p.nB * ((cE + 51) * bandArrayShape p) + (cB + cE + 45)) := by omega
    _ = (cB + cE + 51) * (p.nB * (W + bandArrayShape p) + 1) := by ring

variable {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ' : ℕ → ℤ}

/-- **encodeBandsP**, at the sizes of `p`, for callees described by what they do here: `HB` says
that `bandArray` leaves the list `A β` at `arr`, within `cB bandArrayShape` steps, `HE` that
`encodeP` with the budget `m` turns it into the encoding `E β` at the leaves with at most `m`
symbols `P₀` from `enc + β T`, within `cE encWorkP L m` steps; both in any memory that agrees with
`μ` below `enc`.  Then the encodings `E β` stand from `enc` on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (encodeBands_proc)
theorem encodeBandsP_proc (std : Std lim) (hP : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    {d side aA sI sK cB cE : ℕ} {A : ℕ → List ℤ} {E : ℕ → Leaf p.L → ℤ}
    (pre : BandsPre lim p μ x coefs V) (hd : d < lim.depth)
    (HB : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc →
      Meets lim P pBandArray (d + 1)
        [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, side, aA, sI, sK, x.mask, x.dig3, x.dig4, x.arr]
        μ' (cB * bandArrayShape p) fun _ μ'' =>
          Seg μ'' x.arr (A β) ∧ SameOutside μ' μ'' x.arr p.S7)
    (HE : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc → Seg μ' x.arr (A β) →
      Meets lim P Proc.encodeP (d + 1)
        [p.L, p.m, x.arr, (x.enc + β * p.T : ℕ), x.zs, x.tab, x.p7, x.p10] μ'
        (cE * encWorkP p.L p.m) fun _ μ'' => SegOn p.m μ'' (x.enc + β * p.T) (E β) ∧
          SameOutside2 μ' μ'' (x.enc + β * p.T) (10 ^ p.L) x.zs (7 ^ p.L)) :
    Meets lim P Proc.encodeBandsP d (x.vals p side aA sI sK) μ
      ((cB + cE + 51) * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, SegOn p.m μ' (x.enc + β * p.T) (E β)) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc) := by
  refine .of_body hP (Ends.mono
    (T := p.nB * (cB * bandArrayShape p + cE * encWorkP p.L p.m + 51) + 6) ?_
    (encodeBandsP_time p cB cE) fun _ h => h)
  light_facts pre std
  have hT : p.T = 10 ^ p.L := rfl
  have hS7 : p.S7 = 7 ^ p.L := rfl
  have hnB : p.nB ≤ p.nB * p.T := Nat.le_mul_of_pos_right _ p.one_le_T
  -- for β < nB: the encodings of the bands below β are in place
  refine Ends.forShape
    (fun β r μ' => ⟨frame [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, side, aA, sI, sK,
      x.mask, x.dig3, x.dig4, x.arr, x.zs, x.tab, x.p7, x.p10, x.enc, β, r], μ'⟩)
    (fun β μ' => (∀ β' < β, SegOn p.m μ' (x.enc + β' * p.T) (E β')) ∧
      SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc))
    p.nB (cB * bandArrayShape p + cE * encWorkP p.L p.m + 43) 0
    ⟨fun β' h => absurd h (by omega), .refl⟩
    ?round (fun _ _ h => h) (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
  rintro β r μ' hβ ⟨hdone, same⟩
  have hβT : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
  -- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr)
  light_call (HB β hβ μ' (by light_keep)) with r₁ μ₁ ⟨hA, same₁⟩
  -- encodeP(L, m, arr, enc + β T, zs, tab, p7, p10)
  light_call (HE β hβ μ₁ (by light_keep) hA) with r₂ μ₂ ⟨hEβ, same₂⟩
  refine ⟨r₂, μ₂, rfl, fun β' hβ' => ?_, by light_keep⟩
  rcases Nat.lt_or_ge β' β with h | h
  · -- The encodings of the earlier bands lie below enc + β T and have not been touched.
    have hβ'T : β' * p.T + p.T ≤ β * p.T := Nat.mul_add_le_mul h le_rfl
    exact (hdone β' h).keep
  · obtain rfl : β' = β := by omega
    exact hEβ

/-! ## The two entries -/

/-- encodeBandsP for the row bands of X: side = 0, the coefficients φ at tab.  The encodings are
right at the leaves with at most `m` symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (EncodeBandsLSpec)
def EncodeBandsLSpecP (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aX : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.phiFlat V → MatAt μ aX X → aX + p.N * p.D ≤ x.enc →
    (∀ i j, |X i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P Proc.encodeBandsP d (x.vals p 0 aX p.D 1) μ
      (c * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, SegOn p.m μ' (x.enc + β * p.T)
          (encodingL (bandArrayL (Spec.stdLayout hmL) X β))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

/-- The budget `m ≤ L` fits in a word, since the table of powers of 7 has `L + 1` cells below the
encodings. -/
private theorem BandsPre.m_le_word (std : Std lim) (pre : BandsPre lim p μ x coefs V)
    (hmL : p.m ≤ p.L) : (p.m : ℤ) ≤ lim.word := by
  light_facts pre
  have := std.space_le
  omega

/-- **encodeBandsP** meets this entry, with every constant from cB + cEncP + 51 on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean
-- (encodeBandsL_entry)
theorem encodeBandsPL_entry (std : Std lim) (hP : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {cB c : ℕ} (hB : BandArrayLSpec lim P cB) (hc : cB + cEncP + 51 ≤ c) :
    EncodeBandsLSpecP lim P c := by
  intro p hmL x aX μ X V pre hM hMle hV d hd
  light_facts pre
  refine .mono_const ?_ hc
  refine encodeBandsP_proc std hP pre (by omega)
    (A := fun β => Spec.arrL (bandArrayL (Spec.stdLayout hmL) X β))
    (E := fun β => encodingL (bandArrayL (Spec.stdLayout hmL) X β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aX x.mask x.dig3 x.dig4 x.arr μ' X (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      _ (by omega)
  · exact computeEncoding_phi _ ▸ encodeP_entry leftEquiv phi (by decide) (by decide) phiFlat_spec
      std hS hE (by omega) (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_phiFlat
        omega))
      _ hA (abs_bandArrayL_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word
      (pre.m_le_word std hmL)

/-- encodeBandsP for the column bands of Y: side = 1, the coefficients ψ at tab. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (EncodeBandsRSpec)
def EncodeBandsRSpecP (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aY : ℕ) (μ : ℕ → ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.psiFlat V → MatAt μ aY Y → aY + p.D * p.N ≤ x.enc →
    (∀ i j, |Y i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P Proc.encodeBandsP d (x.vals p 1 aY 1 p.N) μ
      (c * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, SegOn p.m μ' (x.enc + β * p.T)
          (encodingR (bandArrayR (Spec.stdLayout hmL) Y β))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

/-- **encodeBandsP** meets this entry, with every constant from cB + cEncP + 51 on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean
-- (encodeBandsR_entry)
theorem encodeBandsPR_entry (std : Std lim) (hP : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {cB c : ℕ} (hB : BandArrayRSpec lim P cB) (hc : cB + cEncP + 51 ≤ c) :
    EncodeBandsRSpecP lim P c := by
  intro p hmL x aY μ Y V pre hM hMle hV d hd
  light_facts pre
  refine .mono_const ?_ hc
  refine encodeBandsP_proc std hP pre (by omega)
    (A := fun β => Spec.arrR (bandArrayR (Spec.stdLayout hmL) Y β))
    (E := fun β => encodingR (bandArrayR (Spec.stdLayout hmL) Y β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aY x.mask x.dig3 x.dig4 x.arr μ' Y (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      _ (by omega)
  · exact computeEncoding_psi _ ▸ encodeP_entry rightEquiv psi (by decide) (by decide)
      psiFlat_spec std hS hE (by omega) (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_psiFlat
        omega))
      _ hA (abs_bandArrayR_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word
      (pre.m_le_word std hmL)

end Light.Sec2
