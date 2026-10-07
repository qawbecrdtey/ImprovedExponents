module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
public import ImprovedExponents.ParamRoutines.Spec

@[expose] public section

/-!
# The parameter routines at rational exponents

Two routines of the light language, for numerals `a`, `b`, `c`, `d`:

* dRat(n) returns `⌊n^{a/b}⌋` (`dRat_spec`, for `b ≥ 1`): it forms `n^a` by `a` multiplications,
  calls rootCeil(b, n^a + 1) and subtracts 1 (`rootCeil_succ`).
* gRat(D) returns `⌈D^{c/d}⌉` (`gRat_spec`, for `d ≥ 1` and `D ≥ 1`): it forms `D^c` by `c`
  multiplications and calls rootCeil(d, D^c).

Both begin with the same loop (`powThen`, `powThen_ends`).  The times are `tDRat`, `tGRat`, and the
numbers that the routines form are at most `wDRat`, `wGRat`.  Upstream's `d26Body` and `g26Body` are
the model; `gRatBody 63 2000` is the text of `g26Body`.  No routine touches the memory.  As
procedures: `dRat_meets`, `gRat_meets`.
-/

namespace ImprovedExponents.ParamRoutines

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The power of the argument -/

/-- The text with which both routines begin, followed by `s`: local 0 is the argument `x`, local 1
counts the factors, local 2 is their product; `s` starts with `x^e` in local 2. -/
def powThen (e : ℕ) (s : Stmt) : Stmt :=
  .set 1 (k 0) ;;
  .set 2 (k 1) ;;
  .while (v 1 <' k e) (
    .set 2 (v 2 *' v 0) ;;
    .set 1 (v 1 +' k 1)) ;;
  s

/-- **The power loop** takes `12 e + 8` steps and leaves `x^e` in local 2 and `e` in local 1, if
the powers up to `x^e` are at most `B` and `B + e + 1` fits in a word. -/
theorem powThen_ends {μ : ℕ → ℤ} {x e B T : ℕ} {s : Stmt} {Q : State → Prop}
    (hB : ∀ i ≤ e, x ^ i ≤ B) (hword : ((B + e + 1 : ℕ) : ℤ) ≤ lim.word) (hT : 12 * e + 8 ≤ T)
    (h : Ends lim P d s ⟨frame [x, e, (x ^ e : ℕ)], μ⟩ (T - (12 * e + 8)) Q) :
    Ends lim P d (powThen e s) ⟨frame [(x : ℤ)], μ⟩ T Q := by
  push_cast at hword
  have hB0 : (0 : ℤ) ≤ B := Int.natCast_nonneg _
  unfold powThen
  -- cnt := 0; prod := 1
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  -- while cnt < e: prod := prod * x; cnt := cnt + 1.  Before round i, prod = x^i.
  refine Ends.next (12 * e + 4) (Ends.whileBlock
    (fun i σ => σ = ⟨frame [x, i, (x ^ i : ℕ)], μ⟩) e (by simp) ?round ?done
    (by simp; omega)) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hle : ((x ^ (i + 1) : ℕ) : ℤ) ≤ B := by exact_mod_cast hB (i + 1) hi
    have hmul : ((x ^ i : ℕ) : ℤ) * x = ((x ^ (i + 1) : ℕ) : ℤ) := by push_cast; ring
    have hmul0 : (0 : ℤ) ≤ ((x ^ (i + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
    generalize ((x ^ (i + 1) : ℕ) : ℤ) = q' at hle hmul hmul0
    generalize ((x ^ i : ℕ) : ℤ) = q at hmul
    exact ⟨by light_side, by light_side, by light_side [hmul],
      by simp [update_frame_setLocal, hmul]⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_side, by light_side, h.mono (by simp; omega) fun _ hQ => hQ⟩

/-! ## The parameter D -/

/-- dRat(n), over the procedure pRoot (rootCeil): `⌊n^{a/b}⌋`.  Local 0 is the argument, local 2
takes `n^a`, local 1 then takes `⌈(n^a + 1)^{1/b}⌉`. -/
def dRatBody (a b pRoot : ℕ) : Stmt :=
  powThen a (
    .call pRoot [k b, v 2 +' k 1] 1 ;;
    .set 0 (v 1 -' k 1))

/-- The time of dRat. -/
def tDRat (a b n : ℕ) : ℕ := (paramDRatNat a b n + 1) * (16 * b + 27) + 12 * a + 18

/-- A bound on the numbers that dRat forms. -/
def wDRat (a b n : ℕ) : ℕ := (n ^ a + 1) * (paramDRatNat a b n + 1) + a + b + 1

/-- **dRat** returns `⌊n^{a/b}⌋`, for `b ≥ 1`. -/
theorem dRat_spec {μ : ℕ → ℤ} {a b pRoot pPow n : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (hb : b ≠ 0)
    (hword : ((wDRat a b n : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (dRatBody a b pRoot) ⟨frame [(n : ℤ)], μ⟩ (tDRat a b n) fun σ' =>
      σ'.loc 0 = (paramDRatNat a b n : ℕ) ∧ σ'.mem = μ := by
  have hroot : rootCeil b (n ^ a + 1) = paramDRatNat a b n + 1 := rootCeil_succ hb _
  have hpows : ∀ i ≤ a, n ^ i ≤ n ^ a + 1 := fun i hi => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases i with _ | i <;> simp
    · exact (Nat.pow_le_pow_right hn hi).trans (Nat.le_succ _)
  have hmul : n ^ a + 1 ≤ (n ^ a + 1) * (paramDRatNat a b n + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hmul' : paramDRatNat a b n + 1 ≤ (n ^ a + 1) * (paramDRatNat a b n + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold wDRat at hword
  unfold dRatBody tDRat
  generalize hD : paramDRatNat a b n = D at hroot hmul hmul' hword
  generalize hN : n ^ a = N at hroot hmul hmul' hword hpows
  have hfits : (((N + 1) * (D + 1) + b + 1 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (by omega)) hword
  generalize hM : (N + 1) * (D + 1) = M at hmul hmul' hword hfits
  refine powThen_ends (B := N + 1) hpows (le_trans (by exact_mod_cast (by omega)) hword)
    (by omega) ?_
  rw [hN]
  have hN1 : ((N + 1 : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  have hb1 : ((b : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  push_cast at hN1
  -- root := rootCeil(b, n^a + 1)
  refine Ends.callToThen (rootCeil_meets (e := b) (t := N + 1) hR hP hb (by omega)
    (by rw [hroot, hM]; exact hfits) (by omega)) ?_
    (hT := by simp [tRootCeil, hroot]; omega)
  rintro _ μ' ⟨rfl, hμ⟩
  -- return root - 1
  rw [hroot, hμ]
  have hD1 : ((D + 1 : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  push_cast at hD1
  exact Ends.setTo D (by simp) (he := by light_side) (hT := by simp [tRootCeil, hroot]; omega)

/-- **dRat** as a procedure. -/
theorem dRat_meets {μ : ℕ → ℤ} {a b pD pRoot pPow n : ℕ} (hD : P[pD]? = some (dRatBody a b pRoot))
    (hR : P[pRoot]? = some (rootCeilBody pPow)) (hP : P[pPow]? = some powLtBody) (hb : b ≠ 0)
    (hword : ((wDRat a b n : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Meets lim P pD d [(n : ℤ)] μ (tDRat a b n) fun r μ' =>
      r = (paramDRatNat a b n : ℕ) ∧ μ' = μ :=
  Meets.of_body hD (dRat_spec hR hP hb hword hd)

/-! ## The parameter g -/

/-- gRat(D), over the procedure pRoot (rootCeil): `⌈D^{c/d}⌉`, the least `g` with `g^d ≥ D^c`.
Local 0 is the argument, local 2 takes `D^c`. -/
def gRatBody (c d pRoot : ℕ) : Stmt :=
  powThen c (.call pRoot [k d, v 2] 0)

/-- The time of gRat. -/
def tGRat (c d D : ℕ) : ℕ := paramGRatNat c d D * (16 * d + 27) + 12 * c + 12

/-- A bound on the numbers that gRat forms. -/
def wGRat (c d D : ℕ) : ℕ := D ^ c * paramGRatNat c d D + c + d + 1

/-- **gRat** returns `⌈D^{c/d}⌉`, for `d ≥ 1` and `D ≥ 1`. -/
theorem gRat_spec {μ : ℕ → ℤ} {c e pRoot pPow D : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (he : e ≠ 0) (hD : 1 ≤ D)
    (hword : ((wGRat c e D : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (gRatBody c e pRoot) ⟨frame [(D : ℤ)], μ⟩ (tGRat c e D) fun σ' =>
      σ'.loc 0 = (paramGRatNat c e D : ℕ) ∧ σ'.mem = μ := by
  have hpos : 1 ≤ paramGRatNat c e D := one_le_paramGRatNat c e D
  have hmul : D ^ c ≤ D ^ c * paramGRatNat c e D := Nat.le_mul_of_pos_right _ hpos
  have hN0 : 1 ≤ D ^ c := Nat.one_le_pow _ _ hD
  have hpows : ∀ i ≤ c, D ^ i ≤ D ^ c := fun i hi => Nat.pow_le_pow_right hD hi
  unfold wGRat at hword
  unfold gRatBody tGRat
  unfold paramGRatNat at hpos hmul hword ⊢
  generalize hN : D ^ c = N at hpos hmul hword hpows hN0
  have hfits : ((N * rootCeil e N + e + 1 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (by omega)) hword
  generalize hG : rootCeil e N = G at hpos hmul hword hfits
  generalize hM : N * G = M at hmul hword hfits
  refine powThen_ends (B := N) hpows (le_trans (by exact_mod_cast (by omega)) hword)
    (by omega) ?_
  rw [hN]
  have hN1 : ((N : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  have he1 : ((e : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  -- return rootCeil(d, prod)
  exact Ends.callTo (rootCeil_meets (e := e) (t := N) hR hP he hN0
    (by rw [hG, hM]; exact hfits) (by omega)) (fun r μ' h => by simpa [hG] using h)
    (hT := by simp [tRootCeil, hG]; omega)

/-- **gRat** as a procedure. -/
theorem gRat_meets {μ : ℕ → ℤ} {c e pG pRoot pPow D : ℕ} (hG : P[pG]? = some (gRatBody c e pRoot))
    (hR : P[pRoot]? = some (rootCeilBody pPow)) (hP : P[pPow]? = some powLtBody) (he : e ≠ 0)
    (hD : 1 ≤ D) (hword : ((wGRat c e D : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Meets lim P pG d [(D : ℤ)] μ (tGRat c e D) fun r μ' =>
      r = (paramGRatNat c e D : ℕ) ∧ μ' = μ :=
  Meets.of_body hG (gRat_spec hR hP he hD hword hd)

/-- `gRatBody 63 2000` is the text of upstream's `g26Body`. -/
theorem gRatBody_eq_g26Body (pRoot : ℕ) : gRatBody 63 2000 pRoot = g26Body pRoot := rfl

end ImprovedExponents.ParamRoutines
