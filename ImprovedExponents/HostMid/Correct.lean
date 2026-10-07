module

public import ImprovedExponents.HostMid.Time

@[expose] public section

/-!
# The variant host decides Exact Triangle

The specification of the top procedure `et17Body'` of the variant host, from the specifications of
its three parts and of the small case, as upstream's `et17_spec`.
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Correct.lean
/-- **The variant of et17 decides Exact Triangle.**  In every program `P₀ ++ R` that satisfies the
context `Et17Ctx` (it holds the solver, the procedures of the host and the two parameter
procedures), on an instance with `x.Pre μ fr` and within limits that allow for `hostNeed'`, the
body of the variant ends within `hostTime'` steps in a state that satisfies `etTask.Post`. -/
theorem et17_spec' {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    {lim : Limits} {d : ℕ} (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeed' Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Body' ν) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩
      (hostTime' Dfun Gfun tD tG Tn x.n x.U) fun σ' => etTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hparams := et17Params_spec' C x μ fr hpre hok
  have hone : (1 : ℤ) ≤ lim.word := by
    have hword := hok.word
    simp only [hostNeed', hostNeedAt', hostWord] at hword
    omega
  rw [← frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr] 29]
  unfold hostNeed' at hok
  unfold et17Body' hostTime' hostSetup
  generalize Dfun x.n = D at *
  generalize Gfun D = g at *
  -- the parameters
  refine Ends.next _ (hparams.mono le_rfl ?_) (by omega)
  rintro _ rfl
  -- if n is small: the brute force
  by_cases hs : SmallCase x.n D g
  · rw [ite_eq_left hs]
    exact Ends.iteLast (fun _ => (et17Small_spec' C x μ fr D g _ _ hpre hok).mono
      (by simp; omega) fun _ h => h) (fun h => absurd (by simp [et17LocA, hs]) h) (by simp; omega)
  rw [ite_eq_right hs]
  refine Ends.iteLast (fun h => absurd h (by simp [et17LocA, hs])) (fun _ => ?_) (by simp; omega)
  -- otherwise: the sizes, then the tables and the loop over the instances
  have hbig := not_smallCase_iff.1 hs
  have htime := hostRunTime_le' hpre hbig Tn
  refine Ends.next _ ((et17Sizes_spec' C x μ fr D g _ _ hpre hbig hok).mono le_rfl ?_)
    (by unfold hostMain'; simp; omega)
  rintro _ ⟨μ', rfl, hk⟩
  refine (et17Tables_spec' C x μ' fr D g _ _ (hpre.keep hk) hbig hok).mono
    (by unfold hostMain'; simp; omega) ?_
  rintro σ'' ⟨hresult, hk'⟩
  refine ⟨?_, fun a ha => (hk' a ha).trans (hk a ha)⟩
  rw [hresult, HostData.found_m (hostData'_valid hpre hbig), ← flag_eq_bit]
  exact flag_congr (hasZero_iff x.n x.AB x.BC x.AC)

end ImprovedExponents.HostMid
