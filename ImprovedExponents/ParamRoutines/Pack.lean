module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.NeedPolynomial
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Program
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Total

@[expose] public section

/-!
# Theorem 17 for programs, from any pair of parameter routines

Upstream's host of Theorem 17 (`et17`) takes the procedures that compute `D` from `n` and `g` from
`D` as parameters, and upstream instantiates it with two fixed choices, by an assembly that is
private (`ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean`).  This file states that
assembly once, for arbitrary routines.

* `ParamPack D g` bundles everything that is specific to the two routines: the list of procedures,
  the functions they compute, their times and word bounds, and the facts about them.  Nothing in
  it mentions a host.  The times are bounded by the monomial `n² (√D)²` of upstream's scale
  (`StepsMon _ 2 2 0`), which is the largest that `Scale.SoftO.withinBuild` accepts; so they are
  within the bound of Theorem 17 (`ParamPack.stepsD_budget`, `ParamPack.stepsG_budget`), and
  within every other bound that contains `n² D`.
* `ParamPack.host_of_solves` is the part of the assembly that does not depend on which host is
  used: it places the routines behind the solver's program and hands them to a host that is given
  as a hypothesis of the shape of `et17_solves`.
* `claim17_of_paramProcs` is the instance for upstream's host.  Its proof names the four
  host-specific theorems (`et17_solves`, `hostNeed_poly`, `obeysBound17_hostTime`,
  `claim17_of_host`) and the time and the need of the host (`hostTime`, `hostNeed`), and nothing
  else.  A variant of the host with theorems of the same shapes is instantiated by the same term
  with these six names replaced.
-/

namespace ImprovedExponents.ParamRoutines

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3

/-- The procedure number `i` of a list `L` that is placed behind a program `Q` stands at the place
`Q.length + i` of every program that continues `Q ++ L`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean
-- (`paramProcs_get`, private there; here for an arbitrary list)
theorem getElem?_behind (Q L R : Program) {i : ℕ} {body : Stmt} (h : L[i]? = some body) :
    (Q ++ L ++ R)[Q.length + i]? = some body := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R

/-- **The routine-specific part of Theorem 17 for programs**: two parameter routines for the
parameters `D n` and `g n` of the claim, with everything that a host of Theorem 17 needs to know
about them. -/
structure ParamPack (D g : ℕ → ℕ) where
  /-- The procedures to place behind a program of length `o`, as a function of `o`. -/
  procs : ℕ → Program
  /-- The place of the routine for `D` in `procs`. -/
  iD : ℕ
  /-- The place of the routine for `g` in `procs`. -/
  iG : ℕ
  /-- What the routine for `D` computes from `n`. -/
  Dfun : ℕ → ℕ
  /-- What the routine for `g` computes from `D`. -/
  Gfun : ℕ → ℕ
  /-- The time of the routine for `D`, as a function of `n`. -/
  tD : ℕ → ℕ
  /-- The time of the routine for `g`, as a function of `D`. -/
  tG : ℕ → ℕ
  /-- A bound on the numbers that the routine for `D` forms, as a function of `n`. -/
  wD : ℕ → ℕ
  /-- A bound on the numbers that the routine for `g` forms, as a function of `D`. -/
  wG : ℕ → ℕ
  /-- The routine for `D` is a parameter procedure in every program that contains `procs`. -/
  procD : ∀ Q R : Program, ParamProc (Q ++ procs Q.length ++ R) (Q.length + iD) Dfun tD wD
  /-- The routine for `g` is a parameter procedure in every program that contains `procs`. -/
  procG : ∀ Q R : Program, ParamProc (Q ++ procs Q.length ++ R) (Q.length + iG) Gfun tG wG
  /-- `D ≥ 1`. -/
  D_pos : ∀ n, 1 ≤ n → 1 ≤ Dfun n
  /-- `D` is polynomially bounded. -/
  polyD : PolyBounded fun n _ => Dfun n
  /-- `g` is polynomially bounded. -/
  polyG : PolyBounded fun n _ => Gfun (Dfun n)
  /-- The numbers of the routine for `D` are polynomially bounded. -/
  polyWD : PolyBounded fun n _ => wD n
  /-- The numbers of the routine for `g` are polynomially bounded. -/
  polyWG : PolyBounded fun n _ => wG (Dfun n)
  /-- The routine for `D` computes the parameter `D` of the claim. -/
  D_eq : ∀ n, Dfun n = D n
  /-- The routine for `g` computes the parameter `g` of the claim. -/
  G_eq : ∀ n, 1 ≤ n → Gfun (D n) = g n
  /-- The routine for `D` takes `O(n² D)` steps, uniformly in all parameters of Theorem 17 (`θ.D`
  is any `D` with `16 ≤ D ≤ n`, not the value of the routine). -/
  stepsD : StepsMon (fun θ => tD θ.n) 2 2 0
  /-- The routine for `g` takes `O(n² D)` steps, uniformly in all parameters of Theorem 17. -/
  stepsG : StepsMon (fun θ => tG θ.D) 2 2 0

namespace ParamPack

variable {D g : ℕ → ℕ} (pk : ParamPack D g)

/-- The routine for `D` runs within the bound of Theorem 17 (within the term `n² D g`). -/
theorem stepsD_budget : Steps (fun θ => pk.tD θ.n) budget := pk.stepsD.withinBuild

/-- The routine for `g` runs within the bound of Theorem 17 (within the term `n² D g`). -/
theorem stepsG_budget : Steps (fun θ => pk.tG θ.D) budget := pk.stepsG.withinBuild

/-- **The assembly, for any host.**  `solves` is a host in the shape of upstream's `et17_solves`:
from a solver of Lop-AE-SparseTri and two parameter procedures in one program it makes a solver of
Exact Triangle with the time `time` and the need `need`; `poly` says that the need stays
polynomial, as `hostNeed_poly` does.  Then the host over the routines of the pack turns solvers
into solvers, in the form that `claim17_of_host` asks for. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean
-- (`host_of_paramProcs`, private there; here the host is a hypothesis)
theorem host_of_solves {time : (List ℕ → ℕ) → ℕ → ℕ → ℕ}
    {need : (List ℕ → Need) → ℕ → ℕ → Need}
    (solves : ∀ (P₀ : Program) (pS pD pG : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need),
      SolvesN lopDetectTask P₀ pS Tn r →
      (∀ R, ParamProc (P₀ ++ R) pD pk.Dfun pk.tD pk.wD) →
      (∀ R, ParamProc (P₀ ++ R) pG pk.Gfun pk.tG pk.wG) →
      (∀ n, 1 ≤ n → 1 ≤ pk.Dfun n) →
      ∃ (R : Program) (p' : ℕ), Solves etTask (P₀ ++ R) p' (time Tn) (need r))
    (poly : ∀ r, PolyNeedN r → PolyNeed (need r)) :
    ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves etTask (Q ++ R) p' (time Tn) (need r) ∧
        PolyNeed (need r) := by
  intro Q pS Tn r hr hs
  obtain ⟨R, p', h⟩ := solves (Q ++ pk.procs Q.length) pS (Q.length + pk.iD) (Q.length + pk.iG)
    Tn r (hs.append _) (pk.procD Q) (pk.procG Q) pk.D_pos
  rw [List.append_assoc] at h
  exact ⟨_, _, h, poly r hr⟩

end ParamPack

/-- **Theorem 17** for programs of the light language, for any pair of parameter routines:
upstream's host `et17` over the routines of the pack.

The four host-specific theorems are `et17_solves` and `hostNeed_poly` (first argument),
`obeysBound17_hostTime` (second argument) and `claim17_of_host`. -/
theorem claim17_of_paramProcs {D g : ℕ → ℕ} (pk : ParamPack D g) :
    Claim.Theorem_17 lightModel strassen D g :=
  claim17_of_host strassen D g (hostTime pk.Dfun pk.Gfun pk.tD pk.tG)
    (hostNeed pk.Dfun pk.Gfun pk.wD pk.wG)
    (pk.host_of_solves
      (fun _ _ _ _ _ _ hs hD hG hpos => ⟨_, _, et17_solves hs hD hG hpos⟩)
      fun _ hr => hostNeed_poly pk.polyD pk.polyG pk.polyWD pk.polyWG hr)
    (obeysBound17_hostTime D g pk.D_eq pk.G_eq pk.stepsD_budget pk.stepsG_budget)

end ImprovedExponents.ParamRoutines
