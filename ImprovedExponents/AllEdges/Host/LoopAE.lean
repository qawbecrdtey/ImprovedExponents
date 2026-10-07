module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Loop
public import ThreeSumApsp.Lang.Lib.Copy
public import ImprovedExponents.AllEdges.Host.ScanPairsAE
public import ImprovedExponents.AllEdges.Host.Flags

@[expose] public section

/-!
# The loop over the instances of the all-edges host

Upstream's `hostLoop` (`Host/Loop.lean`) treats the instances of the reduction one after the other:
the two matrices, the solver, and the scans of the accepted pairs, while no zero triangle has been
found.  The all-edges variant `hostLoopAE` keeps `n²` flags, one per pair `(a, b)`, in the `n²`
cells below the free pointer `fr` that the solver gets: it fills them with 0 first, and for every
instance it calls `scanPairsAE` instead of `scanPairs`, which scans an accepted pair whose flag is
still 0 and stores the result in the flag.  The loop returns the address of the flags, and after
all instances the flags are those of all-edges Exact Triangle (`hostLoopAE_spec`).

The text has upstream's twenty arguments and locals; the local `Found` holds the address of the
flags.  The specifications of upstream's parts that do not involve the scans (`hostParams_spec`,
`writeX_meets`, `writeY_meets`, `solver_meets`, `hostNext_spec`) are used as they are.
-/

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec HostLocal

variable {lim : Limits} {d : ℕ}

/-! ## The text -/

/-- The four calls for one instance: the two matrices, the solver, the scans with the flags. -/
def hostCallsAE (pS pWriteX pWriteY pScanPairsAE : ℕ) : Stmt :=
  .call pWriteX [v MatX, v ResAC, v Size, v ParD, v ThePrime, v PieceStart, v Len, v Residue]
    Unused ;;
  .call pWriteY [v MatY, v ResBC, v Size, v ParD, v ThePrime, v PieceStart, v Len] Unused ;;
  .call pS [v Size, v ParD, v NumPairs, k 1, v MatX, v MatY, v Rows +' v Start, v Cols +' v Start,
    v AdrOut, v SolverFree] Unused ;;
  .call pScanPairsAE [v AdrOut, v Rows +' v Start, v Cols +' v Start, v NumPairs, v Found, v AdrAB,
    v AdrBC, v AdrAC, v Size, v PieceStart, v Len] Unused

/-- One round of hostLoopAE. -/
def hostRoundAE (pS pWriteX pWriteY pScanPairsAE : ℕ) : Stmt :=
  hostParams ;;
  hostCallsAE pS pWriteX pWriteY pScanPairsAE ;;
  hostNext

/-- hostLoopAE(n, D, p, q, chunkCount, m, ab, bc, ac, rac, rbc, qi, qj, cr, cl, cw, x, y, out, fr):
the flags are the `n²` cells below `fr`; they are returned. -/
def hostLoopAEBody (pS pWriteX pWriteY pScanPairsAE pFill : ℕ) : Stmt :=
  .set Inst (k 0) ;; .set ChunkNo (k 0) ;; .set PieceStart (k 0) ;;
  .set Found (v SolverFree -' (v Size *' v Size)) ;;
  .call pFill [v Found, v Size *' v Size, k 0] Unused ;;
  .while (v Inst <' v NumInst) (hostRoundAE pS pWriteX pWriteY pScanPairsAE) ;;
  .set 0 (v Found)

/-- The number of steps of hostLoopAE, if the solver takes Tn. -/
def tHostLoopAE (Tn : List ℕ → ℕ) (X : HostData) : ℕ :=
  (∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairsAE (X.w t) (X.len t) (X.execsAE t))) + fillTime (X.n * X.n) + 40

/-- The context of hostLoopAE: upstream's `HostCtx` (the solver, the two write routines, the scan),
and the all-edges scan of the pairs and the fill routine. -/
structure HostCtxAE (P₀ R : Program) (pS pWriteX pWriteY pScanPairs pScan pScanPairsAE pFill : ℕ)
    (Tn : List ℕ → ℕ) (need : List ℕ → Need) : Prop extends
    HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need where
  scanPairsAE : (P₀ ++ R)[pScanPairsAE]? = some (scanPairsAEBody pScan)
  fill : (P₀ ++ R)[pFill]? = some fillBody

/-! ## The calls -/

variable {P₀ R : Program} {pS pWriteX pWriteY pScanPairs pScan pScanPairsAE pFill : ℕ}
  {Tn : List ℕ → ℕ} {need : List ℕ → Need} {X : HostData} {U : ℕ} {A : HostAddr} {μ μ' : ℕ → ℤ}
  {t flg : ℕ}

/-- The time of the four calls. -/
def tCallsAE (Tn : List ℕ → ℕ) (X : HostData) (t : ℕ) : ℕ :=
  tWriteX X.n X.D (X.len t) + tWriteY X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairsAE (X.w t) (X.len t) (X.execsAE t) + 52

/-- The flags of the all-edges host lie in the `n²` cells below the solver's free pointer, above
the answers of every instance. -/
structure FlagsPlace (X : HostData) (A : HostAddr) (flg : ℕ) : Prop where
  fr : flg + X.n * X.n = A.fr
  x : A.x ≤ flg
  out : ∀ t < X.m, A.out + X.w t ≤ flg

/-- The call of scanPairsAE for instance t, once the solver has answered: the flags are updated,
and nothing else changes. -/
theorem HostCtxAE.scanPairsAE_meets
    (C : HostCtxAE P₀ R pS pWriteX pWriteY pScanPairs pScan pScanPairsAE pFill Tn need)
    (S : HostSetting lim d X U A need μ μ') (hF : FlagsPlace X A flg) (ht : t < X.m)
    (hans : Seg μ' A.out (X.ans t)) (hflags : Seg μ' flg (X.flagsAt t)) :
    Meets lim (P₀ ++ R) pScanPairsAE (d + 1)
      [(A.out : ℤ), (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), X.w t, flg, A.ab, A.bc, A.ac, X.n,
        X.c0 t, X.len t] μ' (tScanPairsAE (X.w t) (X.len t) (X.execsAE t))
      fun _ μ₁ => Seg μ₁ flg (X.flagsAt (t + 1)) ∧ SameOutside μ' μ₁ flg (X.n * X.n) := by
  have hplaces := S.places ht
  have hout := hF.out t ht
  have hfr := hF.fr
  have hcongr : ∀ i < X.w t, accOf (X.ans t) i = X.acc t i ∧
      hitOf X.n X.AB X.BC X.AC (X.WI t) (X.WJ t) (X.c0 t) (X.len t) i = X.hit t i ∧
      idxOf X.n (X.WI t) (X.WJ t) i = X.pairIdx t i :=
    fun i hi => ⟨rfl, rfl, (X.pairIdx_eq hi).symm⟩
  have hstep := aeStep_congr (X.flagsAt t) hcongr
  have hexecs := aeExecs_congr (X.flagsAt t) hcongr
  refine Meets.of_body C.scanPairsAE ((scanPairsAE_spec C.scan (S.weights ht) (S.answers ht hans)
    (Or.inr hout) (Or.inr (by omega)) (Or.inr (by omega))
    { len := X.length_flagsAt t, seg := hflags, below := by omega
      apartAB := Or.inr (by omega), apartBC := Or.inr (by omega), apartAC := Or.inr (by omega) }
    (by omega) (S.ok.valid.piece_le ht)).mono (le_of_eq ?_) ?_)
  · rw [hexecs]
    rfl
  · rintro σ' ⟨hseg, hsame⟩
    refine ⟨?_, hsame⟩
    rw [HostData.flagsAt, HostData.flagsStep_def, ← hstep]
    exact hseg

/-- **The four calls for instance t**: the flags of instance `t + 1` are in place. -/
theorem hostCallsAE_spec
    (C : HostCtxAE P₀ R pS pWriteX pWriteY pScanPairs pScan pScanPairsAE pFill Tn need)
    (S : HostSetting lim d X U A need μ μ') (hF : FlagsPlace X A flg) (ht : t < X.m)
    (hflags : Seg μ' flg (X.flagsAt t)) (ch : ℕ) (res : ℤ) :
    Ends lim (P₀ ++ R) d (hostCallsAE pS pWriteX pWriteY pScanPairsAE)
      (hostState X A t ch (X.c0 t) flg (X.len t) (X.rho t) (X.lo t) (X.w t) res μ')
      (tCallsAE Tn X t) fun σ => ∃ (res' : ℤ) (μ'' : ℕ → ℤ),
        σ = hostState X A t ch (X.c0 t) flg (X.len t) (X.rho t) (X.lo t) (X.w t) res' μ'' ∧
          HostSetting lim d X U A need μ μ'' ∧ Seg μ'' flg (X.flagsAt (t + 1)) := by
  have hplaces := S.places ht
  have hout := hF.out t ht
  have hfr := hF.fr
  have hlen := X.length_flagsAt t
  unfold hostCallsAE tCallsAE
  -- res := writeX(x, rac, n, D, p, c0, len, rho)
  light_call (C.writeX_meets S ht) with r₁ μ₁ ⟨hX, hrest₁⟩
  have S₁ := S.next fun a ha => hrest₁ a (Or.inl ha)
  replace hflags : Seg μ₁ flg (X.flagsAt t) :=
    hflags.keep fun b hb => hrest₁ b (Or.inr (by rw [hlen] at hb; omega))
  -- res := writeY(y, rbc, n, D, p, c0, len)
  light_call (C.writeY_meets S₁ ht) with r₂ μ₂ ⟨hY, hrest₂⟩
  have S₂ := S₁.next fun a ha => hrest₂ a (Or.inl (by omega))
  replace hX : Seg μ₂ A.x (X.matX t) :=
    hX.keep (by light_keep [X.length_matX t])
  replace hflags : Seg μ₂ flg (X.flagsAt t) :=
    hflags.keep fun b hb => hrest₂ b (Or.inr (by rw [hlen] at hb; omega))
  -- res := solver(n, D, w, 1, x, y, qi + lo, qj + lo, out, fr)
  light_call (C.solver_meets S₂ ht hX hY) with r₃ μ₃ ⟨hans, hkept₃⟩
  have S₃ := S₂.next fun a ha => hkept₃ a (by omega)
  replace hflags : Seg μ₃ flg (X.flagsAt t) :=
    hflags.keep fun b hb => hkept₃ b (by rw [hlen] at hb; omega)
  -- res := scanPairsAE(out, qi + lo, qj + lo, w, flg, ab, bc, ac, n, c0, len)
  light_call (C.scanPairsAE_meets S₃ hF ht hans hflags) with r₄ μ₄ ⟨hflags', hsame⟩
  exact ⟨r₄, μ₄, rfl, S₃.next fun a ha => hsame a (Or.inl (by omega)), hflags'⟩

/-! ## The loop -/

/-- The invariant of the loop, before instance t: upstream's `HostInv` with the address of the
flags in the local `Found`, and the flags of instance `t` in place. -/
def HostInvAE (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr) (flg : ℕ)
    (need : List ℕ → Need) (μ : ℕ → ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ (len rho lo w res : ℤ) (μ' : ℕ → ℤ),
    σ = hostState X A t (t % X.chunkCount) (X.c0 t) flg len rho lo w res μ' ∧
    HostSetting lim d X U A need μ μ' ∧ Seg μ' flg (X.flagsAt t)

/-- **One round of the loop.** -/
theorem hostRoundAE_spec
    (C : HostCtxAE P₀ R pS pWriteX pWriteY pScanPairs pScan pScanPairsAE pFill Tn need)
    (hF : FlagsPlace X A flg) (ht : t < X.m) {σ : State}
    (hσ : HostInvAE lim d X U A flg need μ t σ) :
    Ends lim (P₀ ++ R) d (hostRoundAE pS pWriteX pWriteY pScanPairsAE) σ (tCallsAE Tn X t + 45)
      (HostInvAE lim d X U A flg need μ (t + 1)) := by
  obtain ⟨len, rho, lo, w, res, μ', rfl, S, hflags⟩ := hσ
  unfold hostRoundAE
  -- the parameters of the instance
  light_piece (hostParams_spec S ht _ len rho lo w res) with _ rfl
  -- the four calls
  light_piece (hostCallsAE_spec C S hF ht hflags _ res) with _ ⟨res', μ'', rfl, S', hflags'⟩
  -- the counters
  light_piece (hostNext_spec S' ht _ _ _ _ _ res') with _ rfl
  exact ⟨_, _, _, _, _, μ'', rfl, S', hflags'⟩

/-- **hostLoopAE** returns the address of the flags, which hold the flags of all-edges Exact
Triangle, and changes no cell below x. -/
theorem hostLoopAE_spec
    (C : HostCtxAE P₀ R pS pWriteX pWriteY pScanPairs pScan pScanPairsAE pFill Tn need)
    (hok : HostOk X U) (hmem : HostMem X A μ) (hlay : HostLay X A)
    (hlim : HostLim lim d X U A need) (hF : FlagsPlace X A flg) :
    Ends lim (P₀ ++ R) d (hostLoopAEBody pS pWriteX pWriteY pScanPairsAE pFill)
      ⟨frame (hostLoopArgs X A), μ⟩ (tHostLoopAE Tn X) fun σ' =>
      σ'.loc 0 = flg ∧ Seg σ'.mem flg (ImprovedExponents.AllEdges.aeFlags X.n X.AB X.BC X.AC) ∧
        Kept μ σ'.mem A.x := by
  have hw := hlim.space
  have hfr := hlim.fr
  have hflg := hF.fr
  have hT : ∑ t ∈ Finset.range X.m, (4 + (tCallsAE Tn X t + 45))
      ≤ ∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
        tScanPairsAE (X.w t) (X.len t) (X.execsAE t)) :=
    Finset.sum_le_sum fun t _ => by simp [tCallsAE, tWrites]; omega
  have hflgZ : ((A.fr : ℕ) : ℤ) - (X.n : ℤ) * (X.n : ℤ) = (flg : ℕ) := by
    rw [← hflg]
    push_cast
    ring
  have hx := hF.x
  have hdepth := hlim.depth
  unfold hostLoopAEBody tHostLoopAE hostLoopArgs
  -- t := 0; ch := 0; c0 := 0; fnd := fr - n²
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (flg : ℕ) using hflgZ
  -- fill(fnd, n², 0)
  light_call (fill_meets (lim := lim) (d := d + 1) (x := (0 : ℤ)) C.fill hw
    (by rw [hflg]; omega)) with r₀ μ₁ ⟨hzero, hsame⟩
  -- while t < m
  refine Ends.next _ (Ends.while (HostInvAE lim d X U A flg need μ) X.m
    (fun t => tCallsAE Tn X t + 45) ?start ?round ?done)
    (by simp only [Cond.cost, Expr.cost, List.map, List.sum_cons, List.sum_nil, Nat.reduceAdd]
        omega)
  case start =>
    refine ⟨0, 0, 0, 0, r₀, μ₁, ?_,
      ⟨hok, hmem, hlay, hlim, fun a ha => hsame a (Or.inl (by omega))⟩, hzero⟩
    rw [hostState]
    simp only [HostData.c0, Nat.zero_div, Nat.zero_mul, Nat.cast_zero, Nat.zero_mod, setLocal]
  case round =>
    intro t σ ht hσ
    obtain ⟨len, rho, lo, w, res, μ', rfl, -, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simpa using ht, hostRoundAE_spec C hF ht hσ⟩
  case done =>
    rintro _ ⟨len, rho, lo, w, res, μ', rfl, S, hflags⟩
    rw [X.flagsAt_m hok.valid] at hflags
    -- return fnd
    exact ⟨⟨trivial, trivial⟩, by simp, Ends.setTo (flg : ℕ) ⟨by simp, hflags, S.kept⟩
      (hT := by
        simp only [Cond.cost, Expr.cost, List.map, List.sum_cons, List.sum_nil, Nat.reduceAdd]
        omega)⟩

end Light.Sec3
