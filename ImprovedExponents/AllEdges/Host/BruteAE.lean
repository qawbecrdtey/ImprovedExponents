module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.BruteForce
public import ImprovedExponents.AllEdges.Task

@[expose] public section

/-!
# Brute force for all-edges Exact Triangle

Upstream's `brute` (the small case of Theorem 19) scans all of `C` for every pair `(a, b)` and
returns one bit.  The variant bruteAE(n, U, ab, bc, ac, fr) stores the result of the scan for
`(a, b)` in the cell `fr + a n + b`, so that the `n²` cells from `fr` hold the flags of the task
(`aeFlags`) when it ends (`bruteAE_spec`, `bruteAE_meets`), and returns `fr`.  It takes
`tBruteAE n = 110 n³ + 100` steps.
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 Light.Sec3.Brute ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- One pair `(a, b)`: res := scan(ab, bc, ac, n, a, b, 0, n); M (fr + a n + b) := res.  The locals
are those of upstream's `brute`: `Res` is the result of the scan. -/
def bruteAEPair (pScan : ℕ) : Stmt :=
  .call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, v VtxA, v VtxB, k 0, v Size] Res ;;
  .store (v Free +' v VtxA *' v Size +' v VtxB) (v Res)

/-- The inner loop of bruteAE: all `b` for one `a`. -/
def bruteAEInner (pScan : ℕ) : Stmt := Stmt.for VtxB (v Size) (bruteAEPair pScan)

/-- bruteAE(n, U, ab, bc, ac, fr); the parameter is the procedure number of `scan`. -/
def bruteAEBody (pScan : ℕ) : Stmt :=
  Stmt.for VtxA (v Size) (bruteAEInner pScan) ;; .set 0 (v Free)

/-- The time of bruteAE. -/
def tBruteAE (n : ℕ) : ℕ := 110 * n ^ 3 + 100

/-- The flags of the pairs `(a', b')` before `(a, b)` in the order of the rows, written from `fr`:
the cells `fr + q` for `q < a n + b`. -/
noncomputable def bruteAEMem (μ : ℕ → ℤ) (fr n : ℕ) (AB BC AC : List ℤ) (q : ℕ) : ℕ → ℤ :=
  wrote μ fr (fun q => (aeFlags n AB BC AC).getD q 0) q

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}

/-- Writing the flag of `(a, b)` after those of the earlier pairs. -/
theorem bruteAEMem_succ (ha : a < n) {b : ℕ} (hb : b < n) :
    Function.update (bruteAEMem μ fr n AB BC AC (a * n + b)) (fr + (a * n + b))
      (bit (scanHit n AB BC AC a b 0 n)) = bruteAEMem μ fr n AB BC AC (a * n + b + 1) := by
  rw [bruteAEMem, bruteAEMem, ← wrote_succ, aeFlags_getD_eq_bit_scanHit _ _ _ ha hb]

/-- The flags are not where the weights are. -/
theorem weights_bruteAEMem (C : Weights lim μ ab bc ac n U AB BC AC) (hfr : ab + n * n ≤ fr)
    (hfr' : bc + n * n ≤ fr) (hfr'' : ac + n * n ≤ fr) (q : ℕ) :
    Weights lim (bruteAEMem μ fr n AB BC AC q) ab bc ac n U AB BC AC := by
  light_facts C C.arrAB C.arrBC C.arrAC
  exact
    { C with
      arrAB := C.arrAB.keep fun y hy => wrote_rest (by omega)
      arrBC := C.arrBC.keep fun y hy => wrote_rest (by omega)
      arrAC := C.arrAC.keep fun y hy => wrote_rest (by omega) }

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/BruteForce.lean
/-- One pair: its flag is written. -/
theorem bruteAEPair_spec {b : ℕ} {r : ℤ} (hP : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (hfr : ab + n * n ≤ fr) (hfr' : bc + n * n ≤ fr)
    (hfr'' : ac + n * n ≤ fr) (hlim : fr + n * n ≤ lim.space) (hd : d < lim.depth) (ha : a < n)
    (hb : b < n) :
    Ends lim P d (bruteAEPair pScan)
      ⟨frame [n, U, ab, bc, ac, fr, a, b, 0, r], bruteAEMem μ fr n AB BC AC (a * n + b)⟩
      (tScan n + 24) fun σ' => ∃ r', σ' = ⟨frame [n, U, ab, bc, ac, fr, a, b, 0, r'],
        bruteAEMem μ fr n AB BC AC (a * n + b + 1)⟩ := by
  light_facts C C.arrAB C.arrBC C.arrAC
  have C' := weights_bruteAEMem C hfr hfr' hfr'' (a * n + b)
  have hidx : a * n + b < n * n := Nat.mul_add_lt_mul ha hb
  -- res := scan(ab, bc, ac, n, a, b, 0, n)
  light_call (scan_meets hP C' ha hb (c0 := 0) (Nat.zero_add n).le) with _ _ ⟨rfl, rfl⟩
  rw [flag_eq_bit]
  -- M (fr + a n + b) := res
  refine Ends.storeTo (fr + (a * n + b) : ℕ) (bit (scanHit n AB BC AC a b 0 n))
    ⟨bit (scanHit n AB BC AC a b 0 n), ?_⟩
  rw [bruteAEMem_succ ha hb]
  simp

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/BruteForce.lean
/-- The inner loop: all `b` for one `a`. -/
theorem bruteAEInner_spec {b₀ r₀ : ℤ} (hP : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (hfr : ab + n * n ≤ fr) (hfr' : bc + n * n ≤ fr)
    (hfr'' : ac + n * n ≤ fr) (hlim : fr + n * n ≤ lim.space) (hd : d < lim.depth)
    (hn : n ≤ lim.space) (ha : a < n) :
    Ends lim P d (bruteAEInner pScan)
      ⟨frame [n, U, ab, bc, ac, fr, a, b₀, 0, r₀], bruteAEMem μ fr n AB BC AC (a * n)⟩
      (n * (24 * n + 67) + 6) fun σ' => ∃ r, σ' = ⟨frame [n, U, ab, bc, ac, fr, a, n, 0, r],
        bruteAEMem μ fr n AB BC AC ((a + 1) * n)⟩ := by
  have hw := C.hw
  -- for b < n
  refine Ends.for (fun b σ => ∃ r, σ = ⟨frame [n, U, ab, bc, ac, fr, a, b, 0, r],
    bruteAEMem μ fr n AB BC AC (a * n + b)⟩) n (tScan n + 24)
    ?start ?round ?done ?bound (hT := by simp [tScan]; ring_nf; omega)
  case start => exact ⟨r₀, by simp [update_frame_setLocal]⟩
  case bound =>
    rintro b _ - - ⟨r, rfl⟩
    simp
  case round =>
    rintro b _ hb - ⟨r, rfl⟩
    refine (bruteAEPair_spec hP C hfr hfr' hfr'' hlim hd ha hb).mono le_rfl ?_
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, r', by simp [update_frame_setLocal, Nat.add_assoc]⟩
  case done =>
    rintro _ - ⟨r, rfl⟩
    exact ⟨r, by rw [Nat.add_mul, Nat.one_mul]⟩

end

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/BruteForce.lean
/-- The steps of the two loops of bruteAE are within its time. -/
theorem tBruteAE_ge (n : ℕ) : n * (1 + (n * (24 * n + 67) + 6) + 7) + 8 ≤ tBruteAE n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tBruteAE]
  · have hsq : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by omega)
    have hlin : n ≤ n ^ 3 := Nat.le_self_pow (by omega) n
    rw [show n * (1 + (n * (24 * n + 67) + 6) + 7) = 24 * n ^ 3 + 67 * n ^ 2 + 14 * n by ring,
      tBruteAE]
    omega

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/BruteForce.lean
/-- **The brute force for all-edges Exact Triangle.**  In any program that holds `scanBody` as its
procedure number `pScan`, `bruteAEBody pScan` ends within `tBruteAE n` steps, writes the `n²` flags
of the instance to the cells from `fr`, changes no other cell, and returns `fr`. -/
theorem bruteAE_spec {pScan : ℕ} (hP : P[pScan]? = some scanBody) (x : TriInst) (μ : ℕ → ℤ)
    (fr : ℕ) (hpre : x.Pre μ fr) (hok : (bruteNeed x.n x.U).Ok lim fr d)
    (hlim : fr + x.n * x.n ≤ lim.space) :
    Ends lim P d (bruteAEBody pScan) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ (tBruteAE x.n)
      fun σ' => σ'.loc 0 = fr ∧ Seg σ'.mem fr (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ σ'.mem fr := by
  have C := hpre.weights hok
  have hw := C.hw
  have hd : d < lim.depth := hok.depth
  have hn : x.n ≤ lim.space :=
    (Nat.le_mul_of_pos_left _ hpre.n_pos).trans ((Nat.le_add_left _ _).trans C.arrAB.below)
  have htime := tBruteAE_ge x.n
  have hfr := hpre.belowAB
  have hfr' := hpre.belowBC
  have hfr'' := hpre.belowAC
  unfold bruteAEBody
  -- for a < n
  refine Ends.next _ (Ends.for (fun a σ => ∃ b r, σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr, a, b,
    0, r], bruteAEMem μ fr x.n x.AB x.BC x.AC (a * x.n)⟩) x.n (x.n * (24 * x.n + 67) + 6)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp; omega)
  case start =>
    refine ⟨0, 0, ?_⟩
    simp only [bruteAEMem, Nat.zero_mul, wrote_zero]
    simpa [update_frame_setLocal] using
      (frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr, 0] 3).symm
  case bound =>
    rintro a _ - - ⟨b, r, rfl⟩
    simp
  case round =>
    rintro a _ ha - ⟨b, r, rfl⟩
    refine (bruteAEInner_spec hP C hfr hfr' hfr'' hlim hd hn ha).mono le_rfl ?_
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, x.n, r', by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ - ⟨b, r, rfl⟩
    -- return fr
    refine Ends.setTo fr ⟨by simp, ?_, ?_⟩ (by simp) (by simp; omega)
    · intro q hq
      rw [length_aeFlags] at hq
      change bruteAEMem μ fr x.n x.AB x.BC x.AC (x.n * x.n) (fr + q) = _
      rw [bruteAEMem, wrote_done hq, List.getD_eq_getElem]
    · intro y hy
      change bruteAEMem μ fr x.n x.AB x.BC x.AC (x.n * x.n) y = μ y
      exact wrote_rest (by simp only [Outside]; omega)

/-- The specification of `bruteAE`, for its callers: the flags stand at `fr`, nothing below `fr`
changes, and the result is `fr`. -/
theorem bruteAE_meets {p pScan : ℕ} (hB : P[p]? = some (bruteAEBody pScan))
    (hP : P[pScan]? = some scanBody) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) (hlim : fr + x.n * x.n ≤ lim.space) :
    Meets lim P p d [x.n, x.U, x.ab, x.bc, x.ac, fr] μ (tBruteAE x.n) fun r μ' =>
      r = fr ∧ Seg μ' fr (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ μ' fr :=
  Meets.of_body hB (bruteAE_spec hP x μ fr hpre hok hlim)

end ImprovedExponents.AllEdges
