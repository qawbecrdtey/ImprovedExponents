module

public import ImprovedExponents.AllEdges.Host.ProgramAE
public import ImprovedExponents.AllEdges.Model
public import ImprovedExponents.Pipeline.Claims

@[expose] public section

/-!
# `Claim17Mid` for the all-edges host

The time `hostTimeAE` of the all-edges host obeys the bound of `Claim17Mid`
(`obeysBound17Mid_hostTimeAE`), so the host proves the claim for the model `lightModelAE` of
all-edges Exact Triangle, over any parameter routines (`claim17MidAE_of_paramProcs`,
`claim17MidAE_of_pack`), and `lightModelAE` has the host of Theorem 17 at the true size of the
middle part at all rational exponents (`midHostRat_ae`), as `lightModel` does (`midHostRat_light`).

The all-edges host differs from the variant host of `ImprovedExponents.HostMid` in what it does
beside the calls of the solver: it reads the answers with flags (`tAnswersAE` for `tAnswers`),
scans up to `n²` more times, once for each flag it sets (`tScanCallAE` for `tScanCall`, and
`falsePositiveBound + n²` scans for `falsePositiveBound + 1`), fills the flags and copies them to
the output.  So, without the solver, its time is at most twice that of the variant host plus
`extraAE`: `O(ng) · O(n²/√D)` for the answers and `O(n² √D)` for the rest (`hostTimeAE_zero_le`,
`steps_extraAE`).  The bound of `Claim17Mid` for the variant host (`obeysBound17Mid_hostTime`),
read over a solver that takes no time, bounds the former; the constant doubles.
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec HostMid ParamRoutines

/-! ## The excess over the variant host -/

/-- What the all-edges host spends beyond twice the time of the variant host, both without the
solver: `49` more steps for each of the at most `⌊n²/√D⌋` query pairs of each of the at most `4ng`
instances, at most `n²` scans beyond the failed ones, the filling of the flags, their copy to the
output, and a constant. -/
noncomputable def extraAE (n D g : ℕ) : ℕ :=
  4 * n * g * (49 * queryCapNat n D) + tScanCallAE (pieceSizeNat D g) * (n * n)
    + fillTime (n * n) + copyTime (n * n) + 32

/-- A solver that takes no time has the largest time `0`. -/
theorem supTime_zero (n D cap : ℕ) : supTime (fun _ => 0) n D cap = 0 := by
  simp [supTime]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/TimeBound/Total.lean
/-- Under the hypotheses of Theorem 17 the host does not fall back on the brute force. -/
theorem not_smallCase_of_hyp {n D g : ℕ} (h16 : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (hg : (g : ℝ) ≤ Real.sqrt D) : ¬ SmallCase n D g := by
  have hgD : g ≤ Nat.sqrt D := by
    rw [Nat.le_sqrt']
    exact_mod_cast (Real.le_sqrt g.cast_nonneg D.cast_nonneg).1 hg
  unfold SmallCase
  omega

/-- Without the solver, the loop of the all-edges host takes at most twice the time of the loop of
the variant host plus the excess without the copy. -/
theorem hostLoopBoundAE_zero_le (n U D g : ℕ) :
    hostLoopBoundAE (fun _ => 0) n U D g
      ≤ 2 * hostLoopBound' (fun _ => 0) n U D g
        + (4 * n * g * (49 * queryCapNat n D) + tScanCallAE (pieceSizeNat D g) * (n * n)
          + fillTime (n * n) + 12) := by
  unfold hostLoopBoundAE hostLoopBound'
  rw [supTime_zero]
  generalize pieceSizeNat D g = q
  generalize queryCapNat n D = cap
  generalize falsePositiveBound n U D = F
  generalize 4 * n * g = A
  have hanswers : A * (tWrites n D q + 0 + tAnswersAE cap)
      ≤ A * (tWrites n D q + 0 + tAnswers cap) + A * (49 * cap) := by
    rw [← Nat.mul_add]
    refine Nat.mul_le_mul_left _ ?_
    unfold tAnswersAE tAnswers
    omega
  have hcall : tScanCallAE q ≤ 2 * tScanCall q := by
    unfold tScanCallAE tScanCall tScan
    omega
  have hscans : tScanCallAE q * (F + n * n)
      ≤ 2 * (tScanCall q * (F + 1)) + tScanCallAE q * (n * n) := by
    have hfails : tScanCallAE q * F ≤ 2 * (tScanCall q * (F + 1)) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul hcall (Nat.le_succ F)
    rw [Nat.mul_add]
    exact Nat.add_le_add_right hfails _
  omega

/-- Without the solver, the all-edges host takes at most twice the time of the variant host plus
the excess, if `n` is not small. -/
theorem hostTimeAE_zero_le {Dfun Gfun : ℕ → ℕ} (tD tG : ℕ → ℕ) {n U D g : ℕ} (hD : Dfun n = D)
    (hG : Gfun D = g) (hs : ¬ SmallCase n D g) :
    hostTimeAE Dfun Gfun tD tG (fun _ => 0) n U
      ≤ 2 * hostTime' Dfun Gfun tD tG (fun _ => 0) n U + extraAE n D g := by
  have h := hostLoopBoundAE_zero_le n U D g
  unfold hostTimeAE hostCoreTime hostTime' extraAE
  rw [hD, hG]
  simp only [ite_eq_right hs]
  unfold hostMainAE hostMain'
  omega

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/TimeBound/Total.lean
/-- The time of the all-edges host is the time of `4ng` calls of the solver plus its time without
the solver, if `n` is not small. -/
theorem hostTimeAE_eq {Dfun Gfun : ℕ → ℕ} (tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) {n U D g : ℕ}
    (hD : Dfun n = D) (hG : Gfun D = g) (hs : ¬ SmallCase n D g) :
    hostTimeAE Dfun Gfun tD tG Tn n U
      = 4 * n * g * supTime Tn n (midSize D g) (queryCapNat n D)
        + hostTimeAE Dfun Gfun tD tG (fun _ => 0) n U := by
  unfold hostTimeAE hostCoreTime
  rw [hD, hG]
  simp only [ite_eq_right hs]
  unfold hostMainAE hostLoopBoundAE
  rw [supTime_zero]
  ring

/-! ## The excess is within the bound -/

/-- What bounds the excess: `ng · n²/√D`, for reading the answers of the instances, plus the three
terms of the bound of Theorem 17. -/
noncomputable def restBoundAE (θ : CostParams) : ℝ :=
  (θ.n : ℝ) * θ.g * ((θ.n : ℝ) ^ 2 / Real.sqrt θ.D) + budget θ

/-- What is within the three terms is within `restBoundAE`. -/
theorem stepsRestAE_of_budget {t : CostParams → ℕ} (h : Steps t budget) : Steps t restBoundAE :=
  h.mono_right fun θ _ => le_add_of_nonneg_left (by positivity)

/-- A piece has `⌈s/g⌉ ≤ s` vertices. -/
theorem steps_pieceSizeNatAE : StepsMon (fun θ => pieceSizeNat θ.D θ.g) 0 1 0 :=
  steps_sqrt.of_le fun θ _ => pieceSizeNat_le_sqrt θ.D θ.g

/-- The `n²` scans that set flags take `O(√D/g) · n² ≤ O(n² √D)` steps. -/
theorem steps_scansAE :
    StepsMon (fun θ => tScanCallAE (pieceSizeNat θ.D θ.g) * (θ.n * θ.n)) 2 1 0 := by
  unfold tScanCallAE tScan
  growth [steps_n, steps_pieceSizeNatAE]

/-- Filling the `n²` flags. -/
theorem steps_fillAE : StepsMon (fun θ => fillTime (θ.n * θ.n)) 2 0 0 := by
  unfold fillTime
  growth [steps_n]

/-- Copying the `n²` flags to the output. -/
theorem steps_copyAE : StepsMon (fun θ => copyTime (θ.n * θ.n)) 2 0 0 := by
  unfold copyTime
  growth [steps_n]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/TimeBound/Total.lean
/-- Reading the answers with flags takes `O(ng) · O(n²/√D)` more steps than without. -/
theorem steps_answersAE :
    Steps (fun θ => 4 * θ.n * θ.g * (49 * queryCapNat θ.n θ.D))
      fun θ => (θ.n : ℝ) * θ.g * ((θ.n : ℝ) ^ 2 / Real.sqrt θ.D) := by
  have hinst : Steps (fun θ => 4 * θ.n * θ.g) fun θ => (θ.n : ℝ) * θ.g :=
    (Steps.const_mul (Dominated.refl _ _)).mul (Dominated.refl _ _)
  have hcap : Steps (fun θ => 49 * queryCapNat θ.n θ.D) fun θ => (θ.n : ℝ) ^ 2 / Real.sqrt θ.D :=
    Steps.const_mul (Dominated.of_le fun _ hθ => cast_queryCapNat_le hθ)
  exact hinst.mul hcap

/-- **The excess is within the bound.**  The summands stand in the order of `extraAE`. -/
theorem steps_extraAE : Steps (fun θ => extraAE θ.n θ.D θ.g) restBoundAE :=
  (steps_answersAE.mono_right fun _ hθ => le_add_of_nonneg_right (budget_nonneg hθ))
  |>.add (stepsRestAE_of_budget steps_scansAE.withinBuild)
  |>.add (stepsRestAE_of_budget steps_fillAE.withinBuild)
  |>.add (stepsRestAE_of_budget steps_copyAE.withinBuild)
  |>.add (stepsRestAE_of_budget (Scale.SoftO.const _).withinBuild)

/-! ## The bound of `Claim17Mid` -/

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/TimeBound/Total.lean
/-- A bound `T` on the time of the solver that is monotone in the number of query pairs bounds its
largest time on the instances of the host. -/
theorem cast_supTime_le {Tn : List ℕ → ℕ} {T : ℕ → ℕ → ℕ → ℝ}
    (hT : ∀ n D w w' : ℕ, 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w') {n D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) (cap : ℕ) : ((supTime Tn n D cap : ℕ) : ℝ) ≤ T n D cap := by
  obtain ⟨w, hw, hsup⟩ : ∃ w ∈ Finset.range (cap + 1),
      (Finset.range (cap + 1)).sup (fun w => Tn [n, D, w]) = Tn [n, D, w] :=
    Finset.exists_mem_eq_sup _ ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ _
  rw [supTime, hsup]
  exact hT n D w cap hn hD (Nat.lt_succ_iff.1 (Finset.mem_range.1 hw))

/-- **The bound of `Claim17Mid` for the all-edges host.**  The hypotheses are those of
`ImprovedExponents.HostMid.obeysBound17Mid_hostTime`: the parameter routines compute `Dfun n` from
`n` and `Gfun D` from `D`, these agree with the parameters `D n` and `g n` of the claim, and the
routines run within the bound. -/
theorem obeysBound17Mid_hostTimeAE (D g : ℕ → ℕ) {Dfun Gfun tD tG : ℕ → ℕ}
    (hDf : ∀ n, Dfun n = D n) (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n)
    (hD : Steps (fun θ => tD θ.n) budget) (hG : Steps (fun θ => tG θ.D) budget) :
    ObeysBound17Mid strassen D g (hostTimeAE Dfun Gfun tD tG) := by
  obtain ⟨C₀, hC₀, hbound⟩ := obeysBound17Mid_hostTime D g hDf hGf hD hG
  obtain ⟨C₁, hC₁, hextra⟩ := steps_extraAE
  refine ⟨2 * C₀ + C₁, by positivity, fun Tn T hT n U κ h16 hDn hg1 hg hκ hU => ?_⟩
  have hθ : CostParams.Hyp ⟨n, D n, g n, U, κ⟩ := ⟨h16, hDn, hg1, hg, hκ, hU⟩
  have hn1 : 1 ≤ n := hθ.one_le_n_nat
  have hD1 : 1 ≤ D n := hθ.one_le_D_nat
  have hmid : 1 ≤ midSize (D n) (g n) := one_le_midSize h16 hg1
  have hs : ¬ SmallCase n (D n) (g n) := not_smallCase_of_hyp h16 hDn hg1 hg
  -- the calls of the solver
  have hsolver := cast_supTime_le hT hn1 hmid (queryCapNat n (D n))
  -- the variant host without the solver, by its bound
  have hzero : ((hostTime' Dfun Gfun tD tG (fun _ => 0) n U : ℕ) : ℝ)
      ≤ bound17Mid strassen D g C₀ (fun _ _ _ => 0) n κ :=
    hbound (fun _ => 0) (fun _ _ _ => 0) (fun _ _ _ _ _ _ _ => by simp) n U κ h16 hDn hg1 hg hκ hU
  -- the excess
  have hex := hextra ⟨n, D n, g n, U, κ⟩ hθ
  have hle := hostTimeAE_zero_le tD tG (hDf n) (hGf n hn1) hs (U := U)
  have hcalls : (4 * (n : ℝ) * g n) * (supTime Tn n (midSize (D n) (g n)) (queryCapNat n (D n)) : ℝ)
      ≤ (4 * (n : ℝ) * g n) * T n (midSize (D n) (g n)) (queryCapNat n (D n)) :=
    mul_le_mul_of_nonneg_left hsolver (by positivity)
  have hquery : 0 ≤ C₁ * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n))) := by positivity
  rw [hostTimeAE_eq tD tG Tn (hDf n) (hGf n hn1) hs]
  rw [queryCapNat_eq n hD1] at hcalls ⊢
  have hle' : ((hostTimeAE Dfun Gfun tD tG (fun _ => 0) n U : ℕ) : ℝ)
      ≤ 2 * (hostTime' Dfun Gfun tD tG (fun _ => 0) n U : ℕ) + (extraAE n (D n) (g n) : ℕ) := by
    exact_mod_cast hle
  simp only [bound17Mid, restBoundAE, budget] at hzero hex ⊢
  push_cast
  linarith [hcalls, hle', hzero, hex, hquery]

/-! ## The claim -/

-- adapted from ImprovedExponents/HostMid/AtParameters.lean
/-- **`Claim17Mid` for all-edges Exact Triangle from parameter routines**, as
`ImprovedExponents.HostMid.claim17Mid_of_paramProcs`: `procs o` is a list of routines to be placed
behind a program of length `o`; its routines number `i` and `j` compute `Dfun n` from `n` and
`Gfun D` from `D` in the times `tD`, `tG`, forming numbers up to `wD`, `wG` (`ParamProc`).  If the
results and the words are polynomially bounded, the routines agree with the parameters `D` and `g`
of the claim, and their times are within the budget of Theorem 17, then the all-edges host proves
`Claim17Mid` for `D` and `g` in the model `lightModelAE`. -/
theorem claim17MidAE_of_paramProcs (D g : ℕ → ℕ) {procs : ℕ → Program}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} {i j : ℕ}
    (hD : ∀ Q R, ParamProc (Q ++ procs Q.length ++ R) (Q.length + i) Dfun tD wD)
    (hG : ∀ Q R, ParamProc (Q ++ procs Q.length ++ R) (Q.length + j) Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n)
    (hpolyD : PolyBounded fun n _ => Dfun n) (hpolyG : PolyBounded fun n _ => Gfun (Dfun n))
    (hpolyWD : PolyBounded fun n _ => wD n) (hpolyWG : PolyBounded fun n _ => wG (Dfun n))
    (hDf : ∀ n, Dfun n = D n) (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n)
    (hstepsD : Steps (fun θ => tD θ.n) budget) (hstepsG : Steps (fun θ => tG θ.D) budget) :
    Claim17Mid lightModelAE strassen D g :=
  claim17MidAE_of_host strassen D g _ _
    (hostAE_of_paramProcs hD hG hpos fun _ => hostNeedAE_poly hpolyD hpolyG hpolyWD hpolyWG)
    (obeysBound17Mid_hostTimeAE D g hDf hGf hstepsD hstepsG)

/-- The all-edges host, for any parameter routines, as `ImprovedExponents.claim17Mid_of_pack`. -/
theorem claim17MidAE_of_pack {D g : ℕ → ℕ} (pk : ParamPack D g) :
    Claim17Mid lightModelAE strassen D g :=
  claim17MidAE_of_paramProcs D g pk.procD pk.procG pk.D_pos pk.polyD pk.polyG pk.polyWD pk.polyWG
    pk.D_eq pk.G_eq pk.stepsD_budget pk.stepsG_budget

/-- **`lightModelAE` has the host of Theorem 17 at the true size of the middle part**, at all
rational exponents `D(n) = ⌊n^{a/b}⌋`, `g = ⌈D^{c/d}⌉`, as `lightModel` does
(`ImprovedExponents.midHostRat_light`). -/
theorem midHostRat_ae : MidHostRat lightModelAE := fun a b c d hb hd hab hcd =>
  (hostBound_iff_claim17Mid _ _ _ _).2 (claim17MidAE_of_pack (paramPackRat a b c d hb hd hab hcd))

end ImprovedExponents.AllEdges
