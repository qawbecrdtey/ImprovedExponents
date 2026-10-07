module

public import ImprovedExponents.AllEdges.Task
public import ImprovedExponents.HostMid.Claim

@[expose] public section

/-!
# The time model in which "Exact Triangle" is the all-edges version

Upstream's deductions between running-time claims are made for an arbitrary reading
`M : DetTimeModel` of "is solved in time `T`", and so are ours (`HostBound`, `Claim17Mid`,
`ExplicitFrom`, `explicitFrom_mid`).  `lightModelAE` is upstream's `lightModel` with one field
changed: `exactTriangle T` says that some procedure solves the all-edges version (`aeTask`) within
`T`.  The other fields are those of `lightModel`, definitionally; in particular a solver of
Lop-AE-SparseTri is the same thing in both models.

So a host that solves `aeTask` from a solver of Lop-AE-SparseTri within the bound of Theorem 17
(charged at the true size of the middle part) gives `Claim17Mid lightModelAE …`
(`claim17MidAE_of_host`), and the arithmetic of `ImprovedExponents.Total` then gives
`ExplicitFrom lightModelAE δ 1`: all-edges Exact Triangle in time `n^{3-δ} log n`.
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec HostMid

/-- Upstream's `lightModel`, with "Exact Triangle" read as all-edges Exact Triangle. -/
noncomputable def lightModelAE : DetTimeModel :=
  { lightModel with exactTriangle := SolvedIn aeTask }

@[simp] theorem lightModelAE_exactTriangle :
    lightModelAE.exactTriangle = SolvedIn aeTask := rfl

@[simp] theorem lightModelAE_lopDetect : lightModelAE.lopDetect = lightModel.lopDetect := rfl

@[simp] theorem lightModelAE_thinProduct :
    lightModelAE.thinProduct = lightModel.thinProduct := rfl

@[simp] theorem lightModelAE_minPlusProduct :
    lightModelAE.minPlusProduct = lightModel.minPlusProduct := rfl

@[simp] theorem lightModelAE_apsp : lightModelAE.apsp = lightModel.apsp := rfl

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Claim.lean
/-- **From an all-edges host to the claim**, as `ImprovedExponents.HostMid.claim17Mid_of_host`:
`time` and `need` are the host's time and need as functions of those of the solver. -/
theorem claim17MidAE_of_host (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ)
    (need : (List ℕ → Need) → ℕ → ℕ → Need)
    (host : ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves aeTask (Q ++ R) p' (time Tn) (need r) ∧ PolyNeed (need r))
    (bound : ObeysBound17Mid MM D g time) :
    Claim17Mid lightModelAE MM D g := by
  obtain ⟨C, hC, bound⟩ := bound
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨Q, pS, Tn, r, hpoly, hsolves, hle⟩ := hT
  obtain ⟨R, p', hs, hp⟩ := host Q pS Tn r hpoly hsolves
  exact ⟨timeUpTo (time Tn), hs.solvedIn hp, fun n κ u h16 hDn hg1 hg hκ hu =>
    timeUpTo_le fun U hU =>
      bound Tn T hle n U κ h16 hDn hg1 hg hκ (hU.trans (max_le hu (by positivity)))⟩

end ImprovedExponents.AllEdges
