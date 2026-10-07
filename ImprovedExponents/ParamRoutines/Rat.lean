module

public import ImprovedExponents.ParamRoutines.Routines
public import ImprovedExponents.ParamRoutines.Pack

@[expose] public section

/-!
# Theorem 17 for programs, with `D = ⌊n^{a/b}⌋` and `g = ⌈D^{c/d}⌉`

The routines `dRatBody a b` and `gRatBody c d` are parameter procedures of the host of Theorem 17,
for all natural numbers `a`, `b`, `c`, `d` with `b ≥ 1` and `d ≥ 1` (`paramProc_dRat`,
`paramProc_gRat`).  The parameters and the numbers that the routines form are polynomially bounded
without any condition on the exponents.

The times are `O(n^{a/b})` and `O(D^{c/d})`: `O(n^k)` if `a ≤ k b`, and `O(D^k)` if `c ≤ k d`
(`steps_tDRat_pow`, `steps_tGRat_pow`).  The bound of Theorem 17 is uniform in all `n`, `D`, `g`
with `16 ≤ D ≤ n` and `1 ≤ g ≤ √D`; here `D` is not tied to the value of the routine.  Upstream
charges the parameter routines to the third term `n² D g`, that is, to the monomial `n² (√D)²`
(`Scale.SoftO.withinBuild`).  A function of `n` alone is `O(n² D)` for all such `D` only if it is
`O(n²)`, and a power of `D` is `O(n² D)` for all `D ≤ n` only if it is `O(D³)`.  So the routines
run within that monomial if `a ≤ 2 b` and `c ≤ 3 d` (`steps_tDRat`, `steps_tGRat`), and for that
monomial these conditions cannot be weakened.  They are the only conditions on the exponents:

* `paramPackRat a b c d` is the pack of the two routines;
* `claim_theorem_17_rat` is Theorem 17 for programs at these parameters;
* `claim_theorem_17_rat_upstream` recovers upstream's `claim_theorem_17₂₆` from the case
  `a/b = 1/18`, `c/d = 63/2000`.

For `c = 0` the parameter `g` is 1 (`paramGRat_zero`).
-/

namespace ImprovedExponents.ParamRoutines

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3

/-! ## The routines as parameter procedures -/

/-- The four routines, placed behind a program of length `o`, at the numbers `o`, …, `o + 3`:
powLt, rootCeil, dRat and gRat. -/
def ratProcs (a b c d o : ℕ) : Program :=
  [powLtBody, rootCeilBody o, dRatBody a b (o + 1), gRatBody c d (o + 1)]

/-- `dRatBody a b` computes `⌊n^{a/b}⌋`. -/
theorem paramProc_dRat {b : ℕ} (hb : b ≠ 0) (a c d : ℕ) (Q R : Program) :
    ParamProc (Q ++ ratProcs a b c d Q.length ++ R) (Q.length + 2) (paramDRatNat a b)
      (tDRat a b) (wDRat a b) := by
  intro lim dep x μ _ _ hw hd
  exact dRat_meets (getElem?_behind Q _ R (i := 2) rfl) (getElem?_behind Q _ R (i := 1) rfl)
    (getElem?_behind Q _ R (i := 0) rfl) hb hw (by omega)

/-- `gRatBody c d` computes `⌈D^{c/d}⌉`. -/
theorem paramProc_gRat {d : ℕ} (hd : d ≠ 0) (a b c : ℕ) (Q R : Program) :
    ParamProc (Q ++ ratProcs a b c d Q.length ++ R) (Q.length + 3) (paramGRatNat c d)
      (tGRat c d) (wGRat c d) := by
  intro lim dep x μ hx _ hw hd'
  exact gRat_meets (getElem?_behind Q _ R (i := 3) rfl) (getElem?_behind Q _ R (i := 1) rfl)
    (getElem?_behind Q _ R (i := 0) rfl) hd hx hw (by omega)

/-! ## The parameters and the words are polynomially bounded -/

/-- `⌊n^{a/b}⌋ ≤ n^a`. -/
theorem polyBounded_paramDRatNat (a b : ℕ) : PolyBounded fun n _ => paramDRatNat a b n :=
  (by growth_poly [] : PolyBounded fun n _ => n ^ a).of_le fun n _ => paramDRatNat_le a b n

/-- `⌈D^{c/d}⌉ ≤ D^c + 1`. -/
theorem polyBounded_paramGRatNat (c d : ℕ) {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => paramGRatNat c d (D n) :=
  (by growth_poly [hD] : PolyBounded fun n _ => D n ^ c + 1).of_le fun n _ =>
    paramGRatNat_le c d (D n)

/-- The numbers of `dRatBody`. -/
theorem polyBounded_wDRat (a b : ℕ) : PolyBounded fun n _ => wDRat a b n := by
  unfold wDRat
  growth_poly [polyBounded_paramDRatNat a b]

/-- The numbers of `gRatBody`. -/
theorem polyBounded_wGRat (c d : ℕ) {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => wGRat c d (D n) := by
  unfold wGRat
  growth_poly [hD, polyBounded_paramGRatNat c d hD]

/-! ## The time of the routines -/

/-- `dRatBody` takes a constant number of steps for each number up to `⌊n^{a/b}⌋ + 1`: `O(n^k)`
steps if `a ≤ k b`. -/
theorem steps_tDRat_pow {a b k : ℕ} (hb : b ≠ 0) (hab : a ≤ k * b) :
    StepsMon (fun θ => tDRat a b θ.n) k 0 0 := by
  have hD : StepsMon (fun θ => paramDRatNat a b θ.n) k 0 0 :=
    ((steps_n.pow k).mono fun i => by fin_cases i <;> simp).of_le fun _ hθ =>
      paramDRatNat_le_pow hb hab hθ.one_le_n_nat
  unfold tDRat
  apply Scale.SoftO.mono
  · growth_rules [hD]
  · intro i
    fin_cases i <;> simp

/-- `gRatBody` takes a constant number of steps for each number up to `⌈D^{c/d}⌉`: `O(D^k)` steps
if `c ≤ k d`. -/
theorem steps_tGRat_pow {c d k : ℕ} (hd : d ≠ 0) (hcd : c ≤ k * d) :
    StepsMon (fun θ => tGRat c d θ.D) 0 (2 * k) 0 := by
  have hG : StepsMon (fun θ => paramGRatNat c d θ.D) 0 (2 * k) 0 :=
    ((steps_D.pow k).mono fun i => by fin_cases i <;> simp [mul_comm]).of_le fun _ hθ =>
      paramGRatNat_le_pow hd hcd hθ.one_le_D_nat
  unfold tGRat
  apply Scale.SoftO.mono
  · growth_rules [hG]
  · intro i
    fin_cases i <;> simp

/-- `dRatBody` takes `O(n²)` steps if `a ≤ 2 b`. -/
theorem steps_tDRat {a b : ℕ} (hb : b ≠ 0) (hab : a ≤ 2 * b) :
    StepsMon (fun θ => tDRat a b θ.n) 2 2 0 :=
  (steps_tDRat_pow hb hab).mono (by decide)

/-- `gRatBody` takes `O(n² D)` steps if `c ≤ 3 d`: it takes a constant number of steps for each
number up to `⌈D^{c/d}⌉ ≤ D³`, and `D ≤ n`. -/
theorem steps_tGRat {c d : ℕ} (hd : d ≠ 0) (hcd : c ≤ 3 * d) :
    StepsMon (fun θ => tGRat c d θ.D) 2 2 0 := by
  have hG : StepsMon (fun θ => paramGRatNat c d θ.D) 2 2 0 :=
    (by growth [steps_n, steps_D] : StepsMon (fun θ => θ.n ^ 2 * θ.D) 2 2 0).of_le fun θ hθ =>
      (paramGRatNat_le_pow hd hcd hθ.one_le_D_nat).trans (by
        rw [pow_succ]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hθ.hDn 2))
  unfold tGRat
  growth [hG]

/-! ## The pack and the claim -/

/-- **The pack of the routines for `D = ⌊n^{a/b}⌋` and `g = ⌈D^{c/d}⌉`**, for `b ≥ 1`, `d ≥ 1`,
`a ≤ 2 b` and `c ≤ 3 d`. -/
def paramPackRat (a b c d : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hab : a ≤ 2 * b) (hcd : c ≤ 3 * d) :
    ParamPack (paramDRat a b) (paramGRatOf a b c d) where
  procs := ratProcs a b c d
  iD := 2
  iG := 3
  Dfun := paramDRatNat a b
  Gfun := paramGRatNat c d
  tD := tDRat a b
  tG := tGRat c d
  wD := wDRat a b
  wG := wGRat c d
  procD := paramProc_dRat (by omega) a c d
  procG := paramProc_gRat (by omega) a b c
  D_pos _ hn := one_le_paramDRatNat (by omega) a hn
  polyD := polyBounded_paramDRatNat a b
  polyG := polyBounded_paramGRatNat c d (polyBounded_paramDRatNat a b)
  polyWD := polyBounded_wDRat a b
  polyWG := polyBounded_wGRat c d (polyBounded_paramDRatNat a b)
  D_eq := paramDRatNat_eq (by omega) a
  G_eq _ hn := paramGRatNat_paramDRat (by omega) a b c (one_le_paramDRat (by omega) a hn)
  stepsD := steps_tDRat (by omega) hab
  stepsG := steps_tGRat (by omega) hcd

/-- **Theorem 17** for programs of the light language, with `D := ⌊n^{a/b}⌋` and
`g := ⌈D^{c/d}⌉`, for natural numbers `a`, `b`, `c`, `d` with `b ≥ 1`, `d ≥ 1`, `a ≤ 2 b` and
`c ≤ 3 d`. -/
theorem claim_theorem_17_rat (a b c d : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hab : a ≤ 2 * b)
    (hcd : c ≤ 3 * d) :
    Claim.Theorem_17 lightModel strassen (paramDRat a b) (paramGRatOf a b c d) :=
  claim17_of_paramProcs (paramPackRat a b c d hb hd hab hcd)

/-- Upstream's `claim_theorem_17₂₆`, "D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉", is the case
`a/b = 1/18`, `c/d = 63/2000`. -/
theorem claim_theorem_17_rat_upstream :
    Claim.Theorem_17 lightModel strassen paramD₂₆ paramG₂₆ :=
  paramDRat_one_eighteen ▸ paramGRatOf_eq_paramG₂₆ ▸
    claim_theorem_17_rat 1 18 63 2000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end ImprovedExponents.ParamRoutines
