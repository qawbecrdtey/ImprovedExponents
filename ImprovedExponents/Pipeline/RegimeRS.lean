module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
public import ImprovedExponents.Pipeline.ThinClaim

@[expose] public section

/-!
# A regime test with a rational exponent

The solver of `ImprovedExponents.Pipeline.ThinClaim` is generic in its regime test. Upstream's test
decides `D^18 ≤ N`. This file adds, for natural numbers `r` and `s`, a procedure `testRS r s` that
decides `D^r ≤ N^s`: it computes `N^s` by a loop and calls upstream's `powLt` (which computes `D^r`
without ever exceeding its bound). The three procedures `powLt`, `testRS r s` and the solver that
calls it (`allRSBody`) are appended to `program31 G` (`programRS G r s`).

The result is `thinClaimRS_of_offlineWithin`: the thin product is solved within the bounds of the
offline routine on the instances with `D ≤ N^ε`, for `ε ≤ s/r`, if the tile fits in the whole
regime `D^r ≤ N^s` (`FitsRS G r s`). `thinClaimRS_of_offlineWithinT` is the same for any offline
routine (`OfflineRoutine`) in a program that begins with `programRS G r s`; it serves the pruned
routine of `ImprovedExponents.PrunedProgram`, whose solver is `allBody Proc.testRS Proc.offline32P`.
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3 Light.Sec4

/-! ## The procedures -/

namespace Proc

/-- The number of `powLt` in `programRS`. -/
abbrev powRS : ℕ := 74
/-- The number of `testRS r s` in `programRS`. -/
abbrev testRS : ℕ := 75
/-- The number of the solver in `programRS`. -/
abbrev allRS : ℕ := 76

end Proc

/-- testRS(N, D) returns 1 if `D^r ≤ N^s` and 0 if not. Local 2 counts, local 3 is `N^count`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean (powLtBody) and
-- ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/RegimeTest.lean (regimeExp)
def testRSBody (r s : ℕ) : Stmt :=
  .set 2 (k 0) ;;
  .set 3 (k 1) ;;
  .while (v 2 <' k s) (.set 3 (v 3 *' v 0) ;; .set 2 (v 2 +' k 1)) ;;
  .set 3 (v 3 +' k 1) ;;
  .call Proc.powRS [v 1, k r, v 3] 0

/-- The solver with the test `testRS` and upstream's routine `offline32`: `allInstances26Body`
pointed at `testRS`. -/
def allRSBody : Stmt := allBody Proc.testRS Proc.offline32

/-- `program31 G` followed by `powLt`, `testRS r s` and the solver. -/
def programRS (G : RatParams) (r s : ℕ) : Program :=
  program31 G ++ [powLtBody, testRSBody r s, allRSBody]

/-- The largest number that `testRS r s` forms on `N`, `D`. -/
def wordRS (r s N D : ℕ) : ℕ := N ^ s * D + N ^ s + D + r + s + 100

/-- The running time of `testRS r s`. -/
def tTestRS (r s : ℕ) : ℕ := 12 * s + 16 * r + 40

/-- `program31 G` has 74 procedures. -/
theorem length_program31 (G : RatParams) : (program31 G).length = 74 := rfl

/-- The three new procedures stand at their numbers. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean (program31_at)
theorem programRS_at (G : RatParams) (r s : ℕ) :
    (programRS G r s)[Proc.powRS]? = some powLtBody ∧
      (programRS G r s)[Proc.testRS]? = some (testRSBody r s) ∧
      (programRS G r s)[Proc.allRS]? = some allRSBody := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [programRS, List.getElem?_append_right (by norm_num [length_program31]),
      length_program31]
    rfl

/-! ## The test -/

/-- **testRS** returns 1 if `D^r ≤ N^s` and 0 if not, and changes no cell. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean (powLt_meets)
-- and ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/RegimeTest.lean (regimeExp_spec)
theorem testRS_meets {lim : Limits} {P : Program} {d : ℕ} (r s : ℕ)
    (hP : P[Proc.testRS]? = some (testRSBody r s)) (hpow : P[Proc.powRS]? = some powLtBody)
    (hd : d + 1 ≤ lim.depth) (N D : ℕ) (hN : 1 ≤ N) (hD : 1 ≤ D)
    (hword : ((wordRS r s N D : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) :
    Meets lim P Proc.testRS d [N, D] μ (tTestRS r s) fun r' μ' =>
      μ' = μ ∧ ((r' = 1 ∧ D ^ r ≤ N ^ s) ∨ (r' = 0 ∧ N ^ s < D ^ r)) := by
  refine .of_body hP ?_
  unfold wordRS at hword
  push_cast at hword
  have hNsD : (0 : ℤ) ≤ (N : ℤ) ^ s * D := by positivity
  have hNs : (0 : ℤ) ≤ (N : ℤ) ^ s := by positivity
  unfold testRSBody tTestRS
  -- cnt := 0; acc := 1
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  -- while cnt < s: acc := acc * N; cnt := cnt + 1.  Before round i, cnt = i and acc = N^i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [N, D, i, ((N ^ i : ℕ) : ℤ)], μ⟩) s (by simp) ?round ?done
    le_rfl) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hle : N ^ (i + 1) ≤ N ^ s := Nat.pow_le_pow_right hN hi
    have hleZ : ((N : ℤ) ^ i) * N ≤ (N : ℤ) ^ s := by
      rw [← pow_succ]
      exact_mod_cast hle
    have hpos : (0 : ℤ) ≤ ((N : ℤ) ^ i) * N := by positivity
    exact ⟨by light_side, by light_side, ⟨by light_side, by light_side⟩,
      by simp [update_frame_setLocal, pow_succ]⟩
  case done =>
    rintro _ rfl
    refine ⟨by light_side, by light_side, ?_⟩
    -- acc := acc + 1
    light_set (N ^ s + 1 : ℕ)
    -- powLt(D, r, N^s + 1)
    have hcall := powLt_meets (lim := lim) (P := P) (d := d + 1) (μ := μ) (g := D) (e := r)
      (t := N ^ s + 1) hpow hD (by push_cast; nlinarith)
    refine Ends.callTo hcall (fun r' μ' h => ?_) (hT := by simp; omega)
    obtain ⟨hr', hμ'⟩ := h
    refine ⟨hμ', ?_⟩
    simp only [frame, setLocal, List.getD_cons_zero]
    rw [hr']
    split_ifs with h
    · exact Or.inl ⟨rfl, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩


/-! ## The regime test and the claim -/

/-- The number `testRS r s` forms is polynomial in `N`, `D`. -/
theorem wordRS_poly (r s N D : ℕ) :
    wordRS r s N D ≤ 2 ^ (8 + r + s) * ((N + 1) * (D + 1)) ^ (s + 1) := by
  set Q := (N + 1) * (D + 1) with hQ
  have hQ1 : 1 ≤ Q := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hNQ : N ≤ Q := by nlinarith
  have hDQ : D ≤ Q := by nlinarith
  have hQp : 1 ≤ Q ^ (s + 1) := Nat.one_le_pow _ _ hQ1
  have hNs : N ^ s ≤ Q ^ (s + 1) :=
    (Nat.pow_le_pow_left hNQ s).trans (Nat.pow_le_pow_right hQ1 (by omega))
  have h1 : N ^ s * D ≤ Q ^ (s + 1) := by
    calc N ^ s * D ≤ Q ^ s * Q := Nat.mul_le_mul (Nat.pow_le_pow_left hNQ s) hDQ
      _ = Q ^ (s + 1) := (pow_succ Q s).symm
  have h2 : D ≤ Q ^ (s + 1) := hDQ.trans (Nat.le_self_pow (by omega) Q)
  have hrs : r + s + 100 ≤ 128 * 2 ^ (r + s) := by
    have := Nat.lt_two_pow_self (n := r + s)
    omega
  have hpow : 2 ^ (8 + r + s) * Q ^ (s + 1) = 256 * (2 ^ (r + s) * Q ^ (s + 1)) := by
    rw [show 8 + r + s = 8 + (r + s) by ring, pow_add]
    ring
  have hX1 : Q ^ (s + 1) ≤ 2 ^ (r + s) * Q ^ (s + 1) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hX2 : 128 * 2 ^ (r + s) ≤ 128 * (2 ^ (r + s) * Q ^ (s + 1)) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hQp)
  unfold wordRS
  rw [hpow]
  omega

/-- **The regime test `D^r ≤ N^s`**, as a `RegimeTest`. -/
def regimeRS (r s : ℕ) : RegimeTest where
  Reg N D := D ^ r ≤ N ^ s
  proc := Proc.testRS
  body := testRSBody r s
  aux P := P[Proc.powRS]? = some powLtBody
  aux_append _ Q h := getElem?_append_of_eq_some h Q
  time := tTestRS r s
  word := wordRS r s
  word_poly := ⟨8 + r + s, s + 1, wordRS_poly r s⟩
  meets haux hP hd N D hN hD hword μ :=
    (testRS_meets r s hP haux hd N D hN hD hword μ).mono le_rfl fun r' μ' h =>
      ⟨h.1, h.2.imp id fun h' => ⟨h'.1, by omega⟩⟩

/-- In the whole regime `D^r ≤ N^s`, the hypotheses of Theorem 30 hold at the parameters `G` from
the threshold on. -/
def FitsRS (G : RatParams) (r s : ℕ) : Prop :=
  ∀ N D₀ : ℕ, D₀ ^ r ≤ N ^ s → G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀)

/-- `FitsRS` is `FitsR` at the test `D^r ≤ N^s`. -/
theorem fitsR_regimeRS_iff (G : RatParams) (r s : ℕ) : FitsR (regimeRS r s) G ↔ FitsRS G r s :=
  Iff.rfl

/-- **The thin-product claim from an offline routine `O`, with the test `D^r ≤ N^s`.** If the
regime `D^r ≤ N^s` lies where the routine is specified, the instances with `D ≤ N^ε` lie in the
regime (`ε ≤ s/r`), and the routine stays within its bounds there, then the thin product is solved
within these bounds by the procedure `pAll` of a program that begins with `program31 G` and holds
`allBody Proc.testRS O.proc`, the routine and the procedures it calls. -/
theorem thinClaimRS_of_offlineWithinT {P : Program} {G : RatParams} {O : OfflineRoutine}
    {pAll r s : ℕ} {ε γ q : ℝ} (hr : 1 ≤ r) (hfit : ∀ N D : ℕ, D ^ r ≤ N ^ s → O.Ok N D)
    (hP : ∃ Q, P = programRS G r s ++ Q) (hall : P[pAll]? = some (allBody Proc.testRS O.proc))
    (hoff : P[O.proc]? = some O.body) (hauxO : O.aux P) (hε : ε ≤ (s : ℝ) / r)
    (h : OfflineWithinT O.time ε γ q) : ThinClaim lightModel ε γ q := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨hpow, htest, -⟩ := programRS_at G r s
  exact thinClaimR_of_offlineWithin (R := regimeRS r s) hfit hall
    (getElem?_append_of_eq_some htest Q) (getElem?_append_of_eq_some hpow Q) hoff hauxO
    (by rw [programRS, List.append_assoc]; exact at_base58 rfl _)
    (fun N D₀ hN _ hDN => pow_le_pow_of_le_rpow hr hε hN hDN) h

/-- `programRS G r s` holds offline32 and the procedures it calls. -/
theorem offline32Routine_programRS (G : RatParams) (r s : ℕ) :
    (programRS G r s)[Proc.offline32]? = some offline32Body ∧
      (offline32Routine G).aux (programRS G r s) :=
  ⟨getElem?_append_of_eq_some (offline32Routine_program31 G).1 _, _, rfl⟩

/-- **The thin-product claim from the offline routine, with the test `D^r ≤ N^s`.** If the
hypotheses of Theorem 30 hold at `G` in the whole regime `D^r ≤ N^s` (from the threshold on), the
instances with `D ≤ N^ε` lie in the regime (`ε ≤ s/r`), and the offline routine stays within its
bounds there, then the thin product is solved within these bounds by a procedure of
`programRS G r s`. -/
theorem thinClaimRS_of_offlineWithin {G : RatParams} {r s : ℕ} {ε γ q : ℝ} (hr : 1 ≤ r)
    (hfit : FitsRS G r s) (hε : ε ≤ (s : ℝ) / r) (h : OfflineWithin G ε γ q) :
    ThinClaim lightModel ε γ q :=
  thinClaimRS_of_offlineWithinT (O := offline32Routine G) hr hfit ⟨[], (List.append_nil _).symm⟩
    (programRS_at G r s).2.2 (offline32Routine_programRS G r s).1
    (offline32Routine_programRS G r s).2 hε h

end ImprovedExponents
