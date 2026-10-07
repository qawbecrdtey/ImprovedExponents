module

public import ImprovedExponents.HostMid.NeedPolynomial

@[expose] public section

/-!
# Theorem 17 with the solver charged at the smaller inner dimension, as a claim about programs

`Claim17Mid M MM D g` is upstream's `Claim.Theorem_17 M MM D g` with one change: the solver of
Lop-AE-SparseTri is charged `T n (midSize (D n) (g n)) ⌊n²/√D⌋` for an instance, not
`T n (D n) ⌊n²/√D⌋`.  The middle part of an instance of the reduction has only
`midSize D g = ⌈⌊√D⌋/g⌉ ⌊√D⌋` vertices, about `D/g`.  All other terms are upstream's.

As upstream's `Claim.lean`, this file reduces the claim, for programs of the light language, to two
facts about a host: it turns solvers into solvers and keeps their need polynomial, and its time
obeys the bound (`ObeysBound17Mid`, `claim17Mid_of_host`).
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- **Theorem 17 with the inner dimension of the instances made explicit**: upstream's
`Claim.Theorem_17`, except that the instances of Lop-AE-SparseTri have the inner dimension
`midSize (D n) (g n) = ⌈⌊√D⌋/g⌉ ⌊√D⌋` (the number of vertices of the middle part `piece × ℤ_p`)
and the solver is charged accordingly.  The additional time is unchanged. -/
def Claim17Mid (M : DetTimeModel) (MM : ℕ → ℝ) (D g : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ → ℕ → ℕ → ℝ, M.lopDetect T →
    ∃ T' : ℕ → ℝ → ℝ, M.exactTriangle T' ∧
      ∀ (n : ℕ) (κ u : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
        u ≤ (n : ℝ) ^ κ →
        T' n u ≤ 4 * (n : ℝ) * (g n : ℝ) *
            (T n (midSize (D n) (g n)) (queryCap n (D n)) +
              C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
          C * (termScans n (g n) κ + termPrime MM n (D n) + termBuild n (D n) (g n))

/-- The right-hand side of `Claim17Mid`. -/
noncomputable def bound17Mid (MM : ℕ → ℝ) (D g : ℕ → ℕ) (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ) (n : ℕ)
    (κ : ℝ) : ℝ :=
  4 * (n : ℝ) * (g n : ℝ) *
      (T n (midSize (D n) (g n)) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
    C * (termScans n (g n) κ + termPrime MM n (D n) + termBuild n (D n) (g n))

/-- The time of a host, as a function `time` of the time of the solver, obeys the bound of
`Claim17Mid` with some constant: whenever `T` bounds the time `Tn` of the solver, `bound17Mid` with
`T` bounds `time Tn`, under the hypotheses of the theorem. -/
def ObeysBound17Mid (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (Tn : List ℕ → ℕ) (T : ℕ → ℕ → ℕ → ℝ),
    (∀ m d w w' : ℕ, 1 ≤ m → 1 ≤ d → w ≤ w' → (Tn [m, d, w] : ℝ) ≤ T m d w') →
    ∀ (n U : ℕ) (κ : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
      (U : ℝ) ≤ (n : ℝ) ^ κ → (time Tn n U : ℝ) ≤ bound17Mid MM D g C T n κ

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Claim.lean
/-- **From a host to the claim.**  `time` and `need` are the host's time and need as functions of
those of the solver.  A program has a natural number `U` as the bound on the weights and the claim a
real number `u`; the time for `u` is the largest time for a `U ≤ u`. -/
theorem claim17Mid_of_host (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ)
    (need : (List ℕ → Need) → ℕ → ℕ → Need)
    (host : ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves etTask (Q ++ R) p' (time Tn) (need r) ∧ PolyNeed (need r))
    (bound : ObeysBound17Mid MM D g time) :
    Claim17Mid lightModel MM D g := by
  obtain ⟨C, hC, bound⟩ := bound
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨Q, pS, Tn, r, hpoly, hsolves, hle⟩ := hT
  obtain ⟨R, p', hs, hp⟩ := host Q pS Tn r hpoly hsolves
  exact ⟨timeUpTo (time Tn), hs.solvedIn hp, fun n κ u h16 hDn hg1 hg hκ hu =>
    timeUpTo_le fun U hU =>
      bound Tn T hle n U κ h16 hDn hg1 hg hκ (hU.trans (max_le hu (by positivity)))⟩

end ImprovedExponents.HostMid
