module

public import ImprovedExponents.HostMid.Claim

@[expose] public section

/-!
# The time of the variant host obeys the bound of `Claim17Mid`

The time `hostTime'` of the variant host is upstream's `hostTime` over a solver whose parameters
`[n, D, w]` are rewritten to `[n, midSize D g, w]` (`hostTime'_eq`).  So upstream's bound
`obeysBound17_hostTime` applies, with the bound `T` on the time of the solver read at the rewritten
parameters.
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- **The bound of `Claim17Mid` for the variant host.**  The parameter routines compute `Dfun n`
from `n` and `Gfun D` from `D`.  These agree with the parameters `D n` and `g n` of the claim, and
the routines run within the bound.  The hypotheses are those of upstream's
`obeysBound17_hostTime`. -/
theorem obeysBound17Mid_hostTime (D g : ℕ → ℕ) {Dfun Gfun tD tG : ℕ → ℕ}
    (hDf : ∀ n, Dfun n = D n) (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n)
    (hD : Steps (fun θ => tD θ.n) budget) (hG : Steps (fun θ => tG θ.D) budget) :
    ObeysBound17Mid strassen D g (hostTime' Dfun Gfun tD tG) := by
  obtain ⟨C, hC, hbound⟩ := obeysBound17_hostTime D g hDf hGf hD hG
  refine ⟨C, hC, fun Tn T hT n U κ h16 hDn hg1 hg hκ hU => ?_⟩
  -- The bound on the solver as upstream's host sees it.  Where the rewritten inner dimension is 0,
  -- nothing is known about `T`; the largest time of the solver serves there.
  let T' : ℕ → ℕ → ℕ → ℝ := fun m d w =>
    if 1 ≤ midSize d (Gfun d) then T m (midSize d (Gfun d)) w
    else (((Finset.range (w + 1)).sup fun v => Tn [m, midSize d (Gfun d), v] : ℕ) : ℝ)
  have hT' : ∀ m d w w' : ℕ, 1 ≤ m → 1 ≤ d → w ≤ w' →
      ((Tn (midArgs Gfun [m, d, w]) : ℕ) : ℝ) ≤ T' m d w' := by
    intro m d w w' hm _ hw
    change ((Tn [m, midSize d (Gfun d), w] : ℕ) : ℝ) ≤ T' m d w'
    by_cases hmid : 1 ≤ midSize d (Gfun d)
    · simp only [T', ite_eq_left hmid]
      exact hT m _ w w' hm hmid hw
    · simp only [T', ite_eq_right hmid]
      exact_mod_cast Finset.le_sup (f := fun v => Tn [m, midSize d (Gfun d), v])
        (Finset.mem_range.2 (by omega))
  have hn1 : 1 ≤ n := by omega
  have hmid : 1 ≤ midSize (D n) (g n) := one_le_midSize h16 hg1
  have h := hbound (fun ps => Tn (midArgs Gfun ps)) T' hT' n U κ h16 hDn hg1 hg hκ hU
  rw [hostTime'_eq]
  refine h.trans (le_of_eq ?_)
  simp only [bound17, bound17Mid, T', hGf n hn1, ite_eq_left hmid]

end ImprovedExponents.HostMid
