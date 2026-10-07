module

public import ImprovedExponents.HostMid.Total
import all ThreeSumApsp.Programs.Sec3.Theorem17.ClaimAtParameters

@[expose] public section

/-!
# `Claim17Mid` for programs of the light language, over parameter routines

`claim17Mid_of_paramProcs` is the assembly: from a list of routines that is placed behind the
solver and holds two parameter routines (one computes `D` from `n`, the other `g` from `D`), with
polynomially bounded results and words and with times within the budget of Theorem 17, the variant
host proves `Claim17Mid lightModel strassen D g`.  It is generic in the list of routines and in the
parameters; its hypotheses are those that upstream's `claim_theorem_17₅` and `claim_theorem_17₂₆`
feed to `host_of_paramProcs`, `hostNeed_poly` and `obeysBound17_hostTime`.

`claim17Mid₂₆` instantiates it at upstream's routines for "D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉".
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

open private paramProcs wD26 wG26 paramProc_d26 paramProc_g26 polyBounded_paramD₂₆Nat
  polyBounded_paramG₂₆Nat polyBounded_wD26 polyBounded_wG26 steps_tD26 steps_tG26
  from ThreeSumApsp.Programs.Sec3.Theorem17.ClaimAtParameters

/-! ## The host with parameter routines -/

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean
/-- The variant host over two parameter routines, at the places `i` and `j` of a list `procs o` of
routines that stands behind a program of length `o`, turns a solver of Lop-AE-SparseTri into a
solver of Exact Triangle and keeps the need polynomial. -/
theorem host_of_paramProcs' {procs : ℕ → Program} {Dfun Gfun tD tG wD wG : ℕ → ℕ} {i j : ℕ}
    (hD : ∀ Q R, ParamProc (Q ++ procs Q.length ++ R) (Q.length + i) Dfun tD wD)
    (hG : ∀ Q R, ParamProc (Q ++ procs Q.length ++ R) (Q.length + j) Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n)
    (hpoly : ∀ r, PolyNeedN r → PolyNeed (hostNeed' Dfun Gfun wD wG r)) :
    ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves etTask (Q ++ R) p' (hostTime' Dfun Gfun tD tG Tn)
        (hostNeed' Dfun Gfun wD wG r) ∧ PolyNeed (hostNeed' Dfun Gfun wD wG r) := by
  intro Q pS Tn r hr hs
  have h := et17_solves' (P₀ := Q ++ procs Q.length) (hs.append _) (hD Q) (hG Q) hpos
  rw [List.append_assoc] at h
  exact ⟨_, _, h, hpoly r hr⟩

/-- **`Claim17Mid` from parameter routines.**  `procs o` is a list of routines to be placed behind a
program of length `o`; its routines number `i` and `j` compute `Dfun n` from `n` and `Gfun D` from
`D` in the times `tD`, `tG`, forming numbers up to `wD`, `wG` (`ParamProc`).  If the results and the
words are polynomially bounded, the routines agree with the parameters `D` and `g` of the claim, and
their times are within the budget of Theorem 17, then the variant host proves `Claim17Mid` for `D`
and `g`. -/
theorem claim17Mid_of_paramProcs (D g : ℕ → ℕ) {procs : ℕ → Program}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} {i j : ℕ}
    (hD : ∀ Q R, ParamProc (Q ++ procs Q.length ++ R) (Q.length + i) Dfun tD wD)
    (hG : ∀ Q R, ParamProc (Q ++ procs Q.length ++ R) (Q.length + j) Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n)
    (hpolyD : PolyBounded fun n _ => Dfun n) (hpolyG : PolyBounded fun n _ => Gfun (Dfun n))
    (hpolyWD : PolyBounded fun n _ => wD n) (hpolyWG : PolyBounded fun n _ => wG (Dfun n))
    (hDf : ∀ n, Dfun n = D n) (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n)
    (hstepsD : Steps (fun θ => tD θ.n) budget) (hstepsG : Steps (fun θ => tG θ.D) budget) :
    Claim17Mid lightModel strassen D g :=
  claim17Mid_of_host strassen D g _ _
    (host_of_paramProcs' hD hG hpos fun _ => hostNeed_poly' hpolyD hpolyG hpolyWD hpolyWG)
    (obeysBound17Mid_hostTime D g hDf hGf hstepsD hstepsG)

/-! ## The parameters of Section 3.3 -/

/-- **`Claim17Mid`** for programs of the light language, with "D := ⌊n^{1/18}⌋ and g :=
⌈D^{0.0315}⌉", over upstream's parameter routines. -/
theorem claim17Mid₂₆ : Claim17Mid lightModel strassen paramD₂₆ paramG₂₆ :=
  claim17Mid_of_paramProcs paramD₂₆ paramG₂₆ (procs := paramProcs) paramProc_d26 paramProc_g26
    (fun _ hn => one_le_paramD₂₆Nat hn) polyBounded_paramD₂₆Nat
    (polyBounded_paramG₂₆Nat polyBounded_paramD₂₆Nat) polyBounded_wD26 polyBounded_wG26
    paramD₂₆Nat_eq (fun _ hn => paramG₂₆Nat_eq hn) steps_tD26.withinBuild steps_tG26.withinBuild

end ImprovedExponents.HostMid
