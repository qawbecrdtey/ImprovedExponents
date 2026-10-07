module

public import ThreeSumApsp.Programs.Sec4.Corollary26.Claim
public import ThreeSumApsp.Programs.LightModel
public import ImprovedExponents.Pipeline.OfflineWithin

@[expose] public section

/-!
# A thin-product solver at any parameters of the program

Upstream's solver for Corollary 26 is the procedure `allInstances26` of the program
`program31 ratParams26`: it tests whether `D^18 ≤ N`, calls the offline routine `offline32` if so
and the brute force if not (`Light.Sec4.allInstances26_solves`). The same three procedures are in
`program31 G` for every `G : RatParams`. This file redoes the upstream proof for an arbitrary `G`
(it follows `ThreeSumApsp/Programs/Sec4/Corollary26/AllInstances.lean` and `Claim.lean` line by
line; several lemmas there are private and are repeated here).

The solver `allBody` is generic in its two callees:

* the regime test (`RegimeTest`): a procedure that returns 1 on the instances `(N, D)` of a regime
  `Reg N D` and 0 on the others, with its time and the largest number it forms. Upstream's test
  `D^18 ≤ N` is the instance `regime18`; `ImprovedExponents.Pipeline.RegimeRS` adds the test
  `D^r ≤ N^s`;
* the offline routine (`OfflineRoutine`): a procedure that solves the thin product on the
  instances `Ok N D`, with its time and its need. Upstream's routine `offline32` at the parameters
  `G` is the instance `offline32Routine G`; `ImprovedExponents.PrunedProgram` adds the routine with
  the pruned encoder.

A solver has to be right on every instance, so the whole regime of the test must lie where the
routine is specified. For `offline32` this means that the hypotheses of Theorem 30 hold from the
threshold `m₀` on: this is `FitsR R G` (`Fits18 G` for the test of the program). It limits the
ratio `c = a/b` (the tile `√K N₀` must fit into `N`).

The result is `thinClaimR_of_offlineWithin`: if the offline routine stays within its two bounds on
the instances with `D ≤ N^ε` (`OfflineWithinT` of its time; `OfflineWithin` for `offline32`), and
these lie in the regime, then the thin product is solved, in the sense of the time model
`lightModel`, by one procedure whose time on these instances is at most a constant times
`w D^q (log D + 1) + N² (log D + 1)²/D^γ` (`ThinClaim`). `thinClaim_of_offlineWithin` is the case
of the program's test and routine, with `ε ≤ 1/18`.
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec4

/-! ## The statement -/

/-- A time claim for the thin matrix product: one solver for all instances whose time on the
instances with `D ≤ N^ε` is at most a constant times `w D^q (log D + 1) + N² (log D + 1)²/D^γ`,
for `w` wanted positions. (Compare `Claim.Corollary_26_wanted`.) -/
def ThinClaim (M : DetTimeModel) (ε γ q : ℝ) : Prop :=
  ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ → ℝ), M.thinProduct T ∧
    ∀ (N D w : ℕ) (u : ℝ), 1 ≤ N → 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ ε →
      T N D w u ≤ C * (preBound31 γ N D + (w : ℝ) * queryBound31 q D)

/-- A claim for a larger exponent `ε` is a claim for a smaller one: it covers fewer instances. -/
theorem ThinClaim.mono {M : DetTimeModel} {ε ε₀ γ q : ℝ} (hε : ε ≤ ε₀) (h : ThinClaim M ε₀ γ q) :
    ThinClaim M ε γ q := by
  obtain ⟨C, T, hT, hC⟩ := h
  refine ⟨C, T, hT, fun N D w u hN hD hDN => hC N D w u hN hD (hDN.trans ?_)⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hε

/-! ## The two callees -/

/-- A regime test: the procedure number `proc` with the body `body` returns 1 on the instances of
the regime `Reg N D` and 0 on the others, in `time` steps, forming no number above `word N D`, in
every program that holds it and the auxiliary procedures it calls (`aux`). -/
structure RegimeTest where
  /-- The regime: the instances on which the offline routine is called. -/
  Reg : ℕ → ℕ → Prop
  /-- The number of the test procedure. -/
  proc : ℕ
  /-- The body of the test procedure. -/
  body : Stmt
  /-- The auxiliary procedures the test calls are in the program. -/
  aux : Program → Prop
  /-- Appending procedures keeps the auxiliary procedures. -/
  aux_append : ∀ P R, aux P → aux (P ++ R)
  /-- The running time of the test. -/
  time : ℕ
  /-- The largest number the test forms on `N`, `D`. -/
  word : ℕ → ℕ → ℕ
  /-- That number is polynomial in `N` and `D`. -/
  word_poly : ∃ k e : ℕ, ∀ N D : ℕ, word N D ≤ 2 ^ k * ((N + 1) * (D + 1)) ^ e
  /-- The specification of the test. -/
  meets : ∀ {lim : Limits} {P : Program} {d : ℕ}, aux P → P[proc]? = some body →
    d + 1 ≤ lim.depth → ∀ N D : ℕ, 1 ≤ N → 1 ≤ D → ((word N D : ℕ) : ℤ) ≤ lim.word →
    ∀ μ : ℕ → ℤ, Meets lim P proc d [N, D] μ time fun r μ' =>
      μ' = μ ∧ ((r = 1 ∧ Reg N D) ∨ (r = 0 ∧ ¬ Reg N D))

/-- An offline routine for the thin product: the procedure number `proc` with the body `body`
solves the task `thinTask` on the instances `(N, D)` with `Ok N D`, in `time N D w` steps, whenever
the limits allow for `need N D U`, in every program that holds it and the auxiliary procedures it
calls (`aux`). The routine is called at depth `d + 1`; the need is reckoned from the depth `d` of
the caller. -/
structure OfflineRoutine where
  /-- The instances on which the routine is specified. -/
  Ok : ℕ → ℕ → Prop
  /-- The number of the routine. -/
  proc : ℕ
  /-- The body of the routine. -/
  body : Stmt
  /-- The auxiliary procedures the routine calls are in the program. -/
  aux : Program → Prop
  /-- Appending procedures keeps the auxiliary procedures. -/
  aux_append : ∀ P Q, aux P → aux (P ++ Q)
  /-- The running time on `N`, `D` with `w` wanted positions. -/
  time : ℕ → ℕ → ℕ → ℕ
  /-- The time is monotone in the number of wanted positions. -/
  time_mono : ∀ N D w w' : ℕ, w ≤ w' → time N D w ≤ time N D w'
  /-- What the routine needs on `N`, `D` with entries bounded by `U`: the largest number it forms,
  the cells from the free pointer on, the levels of calls below the caller. -/
  need : ℕ → ℕ → ℕ → Need
  /-- The need is polynomial in `N`, `D`, `U`. -/
  need_poly : ∃ s k : ℕ, ∀ N D U : ℕ,
    (need N D U).word ≤ 2 ^ s * ((N + 1) * (D + 1) * (U + 1)) ^ k ∧
    (need N D U).cells ≤ 2 ^ s * ((N + 1) * (D + 1) * (U + 1)) ^ k ∧
    (need N D U).depth ≤ 2 ^ s * ((N + 1) * (D + 1) * (U + 1)) ^ k
  /-- The specification of the routine. -/
  meets : ∀ {lim : Limits} {P : Program} {d : ℕ} {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ},
    aux P → P[proc]? = some body → x.Pre μ fr → Ok x.N x.D → (need x.N x.D x.U).Ok lim fr d →
    Meets lim P proc (d + 1) [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (time x.N x.D x.w) fun r μ' => thinTask.Post x μ fr r μ'

/-- The solver with the regime test number `test` and the offline routine number `off`:
`allInstances26Body` with `test` in place of `regimeTest26` and `off` in place of `offline32`.
Locals 0 to 9 are the arguments, which are passed on as they are; local 10 is the result of the
test. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
def allBody (test off : ℕ) : Stmt :=
  .call test [v 0, v 1] 10 ;;
  .ite (k 0 <' v 10)
    (.call off [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)
    (.call Sec2.pThinBrute [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)

/-- Upstream's solver is `allBody` at upstream's test and routine. -/
theorem allInstances26Body_eq : allInstances26Body = allBody Proc.regimeTest26 Proc.offline32 :=
  rfl

/-- **Upstream's regime test** `D^18 ≤ N` (`regimeTest26`), as a `RegimeTest`. -/
def regime18 : RegimeTest where
  Reg N D := D ^ 18 ≤ N
  proc := Proc.regimeTest26
  body := regimeTest26Body
  aux _ := True
  aux_append _ _ _ := trivial
  time := 336
  word N D := 4 * D + N * D + 100
  word_poly := ⟨7, 2, fun N D => by nlinarith [Nat.zero_le (N * D), Nat.zero_le N]⟩
  meets _ hP _ N D _ hD hword μ :=
    (regimeTest26_meets hP N D hD hword μ).mono le_rfl fun r μ' h =>
      ⟨h.1, h.2.imp id fun h' => ⟨h'.1, by omega⟩⟩

/-! ## Time and need -/

open Classical in
/-- The time of the solver with the test `R` and the routine `O`, for the parameters N, D, w, U. -/
noncomputable def allInstancesTimeR (R : RegimeTest) (O : OfflineRoutine) : List ℕ → ℕ
  | [N, D, w, _] => R.time + 64 + (if R.Reg N D then O.time N D w else 40 * ((w + 1) * (D + 1)))
  | _ => 0

/-- What the solver with the test `R` and the routine `O` needs, for the parameters N, D, w, U:
the largest number formed (by the test, the brute force and the routine), the cells from the free
pointer on (the brute force uses `N + 1`), the levels of calls (the test is called at depth `d + 1`
and needs one more; the routine's are reckoned from `d`). -/
def allInstancesNeedR (R : RegimeTest) (O : OfflineRoutine) : List ℕ → Need
  | [N, D, _, U] =>
    ⟨R.word N D + (100 + D * (U * U)) + (O.need N D U).word, N + 1 + (O.need N D U).cells,
      2 + (O.need N D U).depth⟩
  | _ => ⟨0, 0, 0⟩

/-- The need of the solver allows for the need of the routine. -/
theorem allInstancesNeedR_ok {lim : Limits} {R : RegimeTest} {O : OfflineRoutine}
    {N D w U fr d : ℕ} (ok : (allInstancesNeedR R O [N, D, w, U]).Ok lim fr d) :
    (O.need N D U).Ok lim fr d :=
  ok.mono (by change _ ≤ R.word N D + (100 + D * (U * U)) + _; omega)
    (by change fr + _ ≤ fr + (N + 1 + _); omega) (by change d + _ ≤ d + (2 + _); omega)

/-- `L = ⌈(a/b) m⌉ ≤ a m`. -/
theorem ratParams_L_le_mul (G : RatParams) (m : ℕ) : G.L m ≤ G.a * m := by
  unfold RatParams.L
  have hb := G.hb
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have h : G.a * m ≤ G.b * (G.a * m) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-! ## The limits of offline32 -/

/-- What offline32 at the parameters `G` needs on `N`, `D` with entries bounded by `U`: the
numbers of `Lim31` and the numerals of `G` (with B = (N + 1)^5, which bounds 10^L in the regime,
the three numbers of `Lim30` are at most B³ U², 7 B U and 10 B); the cells of the block of
Theorem 30 behind the two padded matrices; the levels of the recursion. -/
def offline32Need (G : RatParams) (N D U : ℕ) : Need :=
  ⟨1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U)
      + 7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5
      + (G.a * (4 * D) + G.p * (4 * D) + G.b + G.q + G.m₀),
    4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4, G.a * (4 * D) + 12⟩

section need

variable {lim : Limits} {G : RatParams} {N D₀ U fr d : ℕ}

/-- A number that is at most the word of the need of offline32 fits in a word. -/
theorem fits_of_need (ok : (offline32Need G N D₀ U).Ok lim fr d) {n : ℕ}
    (hn : n ≤ 1000 + 100 * D₀ + N * D₀ + D₀ * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U) +
      7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5
        + (G.a * (4 * D₀) + G.p * (4 * D₀) + G.b + G.q + G.m₀)) : (n : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast hn) ok.word

/-- The block of Theorem 30, behind the two padded matrices, ends within the cells of the need. -/
theorem top_le_of_need (hD : 1 ≤ D₀) (H : Hyp30 (parOf G N D₀) (switchOf31 G D₀))
    (ok : (offline32Need G N D₀ U).Ok lim fr d) :
    top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) ≤ lim.space := by
  have hcells : fr + (4 + N + 8 * (N * D₀) + 222 * ((N + 1) ^ 5) ^ 4) ≤ lim.space := ok.cells
  have hblock : top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) - blockAt N D₀ fr
      ≤ 222 * ((N + 1) ^ 5) ^ 4 := top_sub_le_pow H (below H) _
  have hpad : N * D (logFour D₀) ≤ 4 * (N * D₀) :=
    (Nat.mul_le_mul_left N (Nat.pow_clog_le_mul (b := 4) (by norm_num) hD)).trans_eq (by ring)
  have hbase : blockAt N D₀ fr = fr + 3 + N * D (logFour D₀) + N * D (logFour D₀) := rfl
  omega

/-- If B bounds 10^L, 7^L and 10^m, the three numbers in the limits of Theorem 30 are at most B³ U²,
7 B U and 10 B. -/
theorem lim30_of_below {p : Sec2.Par} {t b0 B : ℕ} (hB : Below p t B) (std : Std lim)
    (hspace : top p t b0 ≤ lim.space)
    (fits : ∀ n : ℕ, n ≤ B ^ 3 * (U * U) + 7 * (B * U) + 10 * B → (n : ℤ) ≤ lim.word) :
    Lim30 lim p t b0 (U : ℤ) := by
  have hten := hB.T
  have hseven := hB.S7
  have htenm := hB.tenm
  have hvalue : 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ B ^ 3 * (U * U) :=
    calc 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ B * ((B * U) * (B * U)) := by gcongr
      _ = B ^ 3 * (U * U) := by ring
  have henc : 7 ^ (p.L + 1) * U ≤ 7 * (B * U) :=
    calc 7 ^ (p.L + 1) * U = 7 * (7 ^ p.L * U) := by ring
      _ ≤ 7 * (B * U) := by gcongr
  have hpow : 10 ^ (p.L + 1) ≤ 10 * B :=
    calc 10 ^ (p.L + 1) = 10 * 10 ^ p.L := by ring
      _ ≤ 10 * B := by gcongr
  exact {
    std := std
    space := hspace
    value := by exact_mod_cast fits _ (hvalue.trans (by omega))
    enc := by exact_mod_cast fits _ (henc.trans (by omega))
    pow := fits _ (hpow.trans (by omega)) }

/-- If the hypotheses of Theorem 30 hold from the threshold on, the need of offline32 covers what
it asks of the limits. -/
theorem lim31_of_need (hD : 1 ≤ D₀)
    (hfit : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀))
    (ok : (offline32Need G N D₀ U).Ok lim fr d) : Lim31 lim G N D₀ fr (U : ℤ) := by
  have hcells : fr + (4 + N + 8 * (N * D₀) + 222 * ((N + 1) ^ 5) ^ 4) ≤ lim.space := ok.cells
  have fits {n : ℕ} := fits_of_need ok (n := n)
  have h4 : 4 ^ logFour D₀ ≤ 4 * D₀ := Nat.pow_clog_le_mul (b := 4) (by norm_num) hD
  have hm4 : logFour D₀ ≤ 4 * D₀ := logFour_le_four_mul hD
  have ha : G.a * logFour D₀ ≤ G.a * (4 * D₀) := Nat.mul_le_mul_left _ hm4
  have hp : G.p * logFour D₀ ≤ G.p * (4 * D₀) := Nat.mul_le_mul_left _ hm4
  have std : Std lim := ⟨ok.space, by exact_mod_cast fits (n := 100) (by omega)⟩
  have large (hm : G.m₀ ≤ logFour D₀) : Lim30 lim (parOf G N D₀) (switchOf31 G D₀)
      (blockAt N D₀ fr) (U : ℤ) :=
    have H := hfit hm
    lim30_of_below (B := (N + 1) ^ 5) (below H) std (top_le_of_need hD H ok)
      fun n hn => fits (hn.trans (by omega))
  exact {
    std := std
    space := by
      unfold structEnd
      split_ifs with h
      · omega
      · exact (large (not_lt.mp h)).space
    pow := fits (by omega)
    mword := fits (by omega)
    m0word := fits (n := G.m₀) (by omega)
    ip := by exact_mod_cast fits (n := D₀ * (U * U)) (by omega)
    large := large }

end need

/-! ## Upstream's routine -/

/-- **Where the hypotheses of Theorem 30 hold from the threshold on**, offline32 solves the
task. -/
theorem offline32_meets_thinTask {lim : Limits} {P : Program} {G : RatParams} {c d : ℕ}
    (task : OfflineSpec32 lim P c G) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hfit : G.m₀ ≤ logFour x.D → Hyp30 (parOf G x.N x.D) (switchOf31 G x.D))
    (ok : (offline32Need G x.N x.D x.U).Ok lim fr d) :
    Meets lim P Proc.offline32 (d + 1) [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (tOffline32 c G x.N x.D x.w) fun r μ' => thinTask.Post x μ fr r μ' := by
  have hU0 : (0 : ℤ) ≤ (x.U : ℤ) := by positivity
  have hdepth : d + (G.a * (4 * x.D) + 12) ≤ lim.depth := ok.depth
  have hm4 := logFour_le_four_mul hpre.D_pos
  have hL : G.L (logFour x.D) ≤ G.a * (4 * x.D) :=
    (ratParams_L_le_mul G _).trans (Nat.mul_le_mul_left _ hm4)
  have spec := task x.N x.D x.x x.y x.wi x.wj x.out fr (thinMX x) (thinMY x) (x.U : ℤ) (x.U : ℤ) μ
    x.WI x.WJ
    { one_le_D := hpre.D_pos, one_le_N := hpre.N_pos
      lim := lim31_of_need hpre.D_pos hfit ok
      absX := fun i j => hpre.leX.abs_getD_le hU0 _
      absY := fun i j => hpre.leY.abs_getD_le hU0 _
      belowX := hpre.belowX, belowY := hpre.belowY }
    { matX := matAt_thinMX hpre, matY := matAt_thinMY hpre
      rows := hpre.segWI, cols := hpre.segWJ
      length_eq := by rw [hpre.lenWI, hpre.lenWJ]
      rows_lt := hpre.ltWI, cols_lt := hpre.ltWJ
      rows_le := by rw [hpre.lenWI]; exact hpre.belowWI
      cols_le := by rw [hpre.lenWI]; exact hpre.belowWJ
      out_le := by rw [hpre.lenWI]; exact hpre.belowOut
      out_matX := by rw [hpre.lenWI]; exact hpre.apartX
      out_matY := by rw [hpre.lenWI]; exact hpre.apartY
      out_rows := by rw [hpre.lenWI]; exact hpre.apartWI
      out_cols := by rw [hpre.lenWI]; exact hpre.apartWJ }
  rw [hpre.lenWI, map_entryN_thin hpre] at spec
  exact (spec _ (by omega)).mono le_rfl fun r μ' h => ⟨h.1, fun a ha => h.2 a ha.1 ha.2⟩

/-- The time of offline32 is monotone in the number of wanted positions. -/
theorem tOffline32_mono (c : ℕ) (G : RatParams) (N D₀ : ℕ) {w w' : ℕ} (hw : w ≤ w') :
    tOffline32 c G N D₀ w ≤ tOffline32 c G N D₀ w' := by
  unfold tOffline32
  have := Nat.mul_le_mul_right (tQuery31 G D₀ + 30) hw
  omega

/-- A program that begins with `program31 G` holds offline32 with its specification at the
parameters `G`, for all limits. -/
theorem offlineSpec32_of_program31 {P : Program} {G : RatParams} (h : ∃ R, P = program31 G ++ R)
    (lim : Limits) : OfflineSpec32 lim P cShared30 G := by
  obtain ⟨R, rfl⟩ := h
  exact (offline32_program31 G lim).append R

theorem le_pow_twenty {Q x : ℕ} (hQ : 1 ≤ Q) (i : ℕ) (hi : i ≤ 20) (h : x ≤ Q ^ i) :
    x ≤ Q ^ 20 :=
  h.trans (Nat.pow_le_pow_right hQ hi)

section summands

variable {N D U Q : ℕ}

/-- The largest number that offline32 forms, apart from the numerals of the parameters. -/
theorem word_le (hN : N + 1 ≤ Q) (hD : D ≤ Q) (hU : U ≤ Q) :
    1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U) +
      7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5 ≤ 2 ^ 11 * Q ^ 20 := by
  have hQ : 1 ≤ Q := by omega
  have hN' : N ≤ Q := by omega
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hD1 : D ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hD)
  have hND : N * D ≤ Q ^ 20 := le_pow_twenty hQ 2 (by norm_num) <|
    calc N * D ≤ Q * Q := by gcongr
      _ = Q ^ 2 := by ring
  have hDUU : D * (U * U) ≤ Q ^ 20 := le_pow_twenty hQ 3 (by norm_num) <|
    calc D * (U * U) ≤ Q * (Q * Q) := by gcongr
      _ = Q ^ 3 := by ring
  have hvalue : ((N + 1) ^ 5) ^ 3 * (U * U) ≤ Q ^ 20 := le_pow_twenty hQ 17 (by norm_num) <|
    calc ((N + 1) ^ 5) ^ 3 * (U * U) ≤ (Q ^ 5) ^ 3 * (Q * Q) := by gcongr
      _ = Q ^ 17 := by ring
  have henc : (N + 1) ^ 5 * U ≤ Q ^ 20 := le_pow_twenty hQ 6 (by norm_num) <|
    calc (N + 1) ^ 5 * U ≤ Q ^ 5 * Q := by gcongr
      _ = Q ^ 6 := by ring
  have hpow : (N + 1) ^ 5 ≤ Q ^ 20 := le_pow_twenty hQ 5 (by norm_num) (by gcongr)
  omega

/-- The cells that offline32 uses. -/
theorem cells_le (hN : N + 1 ≤ Q) (hD : D ≤ Q) :
    4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4 ≤ 2 ^ 11 * Q ^ 20 := by
  have hQ : 1 ≤ Q := by omega
  have hN' : N ≤ Q := by omega
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hN1 : N ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hN')
  have hND : N * D ≤ Q ^ 20 := le_pow_twenty hQ 2 (by norm_num) <|
    calc N * D ≤ Q * Q := by gcongr
      _ = Q ^ 2 := by ring
  have hblock : ((N + 1) ^ 5) ^ 4 ≤ Q ^ 20 :=
    calc ((N + 1) ^ 5) ^ 4 ≤ (Q ^ 5) ^ 4 := by gcongr
      _ = Q ^ 20 := by ring
  omega

end summands

/-- The need of offline32 is polynomial in `N`, `D`, `U`. The numerals of `G` go into the
constant. -/
theorem offline32Need_poly (G : RatParams) : ∃ s k : ℕ, ∀ N D U : ℕ,
    (offline32Need G N D U).word ≤ 2 ^ s * ((N + 1) * (D + 1) * (U + 1)) ^ k ∧
    (offline32Need G N D U).cells ≤ 2 ^ s * ((N + 1) * (D + 1) * (U + 1)) ^ k ∧
    (offline32Need G N D U).depth ≤ 2 ^ s * ((N + 1) * (D + 1) * (U + 1)) ^ k := by
  -- κ bounds the numerals of the parameters
  set κ : ℕ := 4 * G.a + 4 * G.p + G.b + G.q + G.m₀ + 12 with hκ
  refine ⟨12 + κ, 20, fun N D U => ?_⟩
  have hN : N + 1 ≤ (N + 1) * (D + 1) * (U + 1) :=
    Nat.le_mul_of_pos_right _ (by positivity) |>.trans' (Nat.le_mul_of_pos_right _ (by positivity))
  have hD : D ≤ (N + 1) * (D + 1) * (U + 1) :=
    calc D ≤ D + 1 := Nat.le_succ _
      _ ≤ (N + 1) * (D + 1) := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ (N + 1) * (D + 1) * (U + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hU : U ≤ (N + 1) * (D + 1) * (U + 1) :=
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by positivity))
  generalize (N + 1) * (D + 1) * (U + 1) = Q at *
  have hQ : 1 ≤ Q := by omega
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hD1 : D ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hD)
  -- the two constants: 2^11 + κ ≤ 2^(12 + κ)
  have hκ2 : κ ≤ 2 ^ κ := Nat.lt_two_pow_self.le
  have hA : (2 : ℕ) ^ 11 ≤ 2 ^ 11 * 2 ^ κ := Nat.le_mul_of_pos_right _ (by positivity)
  have hB : (2 : ℕ) ^ κ ≤ 2 ^ 11 * 2 ^ κ := Nat.le_mul_of_pos_left _ (by positivity)
  have hpow : (2 : ℕ) ^ (12 + κ) = 2 * (2 ^ 11 * 2 ^ κ) := by
    rw [pow_add]
    ring
  have hsum : (2 ^ 11 + κ) * Q ^ 20 ≤ 2 ^ (12 + κ) * Q ^ 20 :=
    Nat.mul_le_mul_right _ (by rw [hpow]; omega)
  have hmul : (2 ^ 11 + κ) * Q ^ 20 = 2 ^ 11 * Q ^ 20 + κ * Q ^ 20 := by ring
  -- the numerals of the parameters
  have haD : G.a * (4 * D) ≤ 4 * G.a * Q ^ 20 := by
    calc G.a * (4 * D) = 4 * G.a * D := by ring
      _ ≤ 4 * G.a * Q ^ 20 := Nat.mul_le_mul_left _ hD1
  have hpD : G.p * (4 * D) ≤ 4 * G.p * Q ^ 20 := by
    calc G.p * (4 * D) = 4 * G.p * D := by ring
      _ ≤ 4 * G.p * Q ^ 20 := Nat.mul_le_mul_left _ hD1
  have hrest : G.b + G.q + G.m₀ + 12 ≤ (G.b + G.q + G.m₀ + 12) * Q ^ 20 :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hκQ : κ * Q ^ 20 = 4 * G.a * Q ^ 20 + 4 * G.p * Q ^ 20
      + (G.b + G.q + G.m₀ + 12) * Q ^ 20 := by
    rw [hκ]
    ring
  have hw := word_le (U := U) hN hD hU
  have hc := cells_le hN hD
  refine ⟨?_, ?_, ?_⟩
  · change 1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U)
      + 7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5
      + (G.a * (4 * D) + G.p * (4 * D) + G.b + G.q + G.m₀) ≤ _
    omega
  · change 4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4 ≤ _
    have : 0 ≤ κ * Q ^ 20 := Nat.zero_le _
    omega
  · change G.a * (4 * D) + 12 ≤ _
    have : 0 ≤ 2 ^ 11 * Q ^ 20 := Nat.zero_le _
    omega

/-- **Upstream's offline routine** `offline32` at the parameters `G`, as an `OfflineRoutine`: it
is specified on the instances where the hypotheses of Theorem 30 hold from the threshold on, in
the programs that begin with `program31 G`. -/
def offline32Routine (G : RatParams) : OfflineRoutine where
  Ok N D := G.m₀ ≤ logFour D → Hyp30 (parOf G N D) (switchOf31 G D)
  proc := Proc.offline32
  body := offline32Body
  aux P := ∃ R, P = program31 G ++ R
  aux_append _ Q := fun ⟨R, h⟩ => ⟨R ++ Q, by rw [h, List.append_assoc]⟩
  time := tOffline32 cShared30 G
  time_mono N D _ _ hw := tOffline32_mono cShared30 G N D hw
  need := offline32Need G
  need_poly := offline32Need_poly G
  meets haux _ hpre hfit ok :=
    offline32_meets_thinTask (offlineSpec32_of_program31 haux _) hpre hfit ok

/-- `program31 G` holds offline32 and the procedures it calls. -/
theorem offline32Routine_program31 (G : RatParams) :
    (program31 G)[Proc.offline32]? = some offline32Body ∧ (offline32Routine G).aux (program31 G) :=
  ⟨program31_at _ Proc.offline32, [], (List.append_nil _).symm⟩

/-- In the whole regime of the test `R`, the hypotheses of Theorem 30 hold at the parameters `G`
from the threshold on: the regime lies where `offline32` is specified. -/
def FitsR (R : RegimeTest) (G : RatParams) : Prop :=
  ∀ N D₀ : ℕ, R.Reg N D₀ → (offline32Routine G).Ok N D₀

/-- In the whole regime `D^18 ≤ N` of the program's test, the hypotheses of Theorem 30 hold at the
parameters `G` from the threshold on. -/
def Fits18 (G : RatParams) : Prop :=
  ∀ N D₀ : ℕ, D₀ ^ 18 ≤ N → G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀)

/-- `Fits18` is `FitsR` at upstream's test. -/
theorem fitsR_regime18_iff (G : RatParams) : FitsR regime18 G ↔ Fits18 G := Iff.rfl

/-- The time of allInstances26 in `program31 G`, for the parameters N, D, w, U. -/
noncomputable def allInstancesTime (G : RatParams) : List ℕ → ℕ :=
  allInstancesTimeR regime18 (offline32Routine G)

/-- What allInstances26 needs in `program31 G`, for the parameters N, D, w, U. -/
def allInstancesNeed (G : RatParams) : List ℕ → Need :=
  allInstancesNeedR regime18 (offline32Routine G)

/-! ## The solver -/

open Classical in
/-- **The solver with the test `R` and the routine `O` solves the task on all instances**, in
every program that holds it, the test, the routine and the brute force at their numbers, with the
procedures the test and the routine call, if the regime lies where the routine is specified; also
after more procedures are appended. -/
theorem allInstances_solves {P : Program} {R : RegimeTest} {O : OfflineRoutine} {pAll : ℕ}
    (hfit : ∀ N D : ℕ, R.Reg N D → O.Ok N D) (hall : P[pAll]? = some (allBody R.proc O.proc))
    (htest : P[R.proc]? = some R.body) (haux : R.aux P) (hoff : P[O.proc]? = some O.body)
    (hauxO : O.aux P) (hbrute : P[Sec2.pThinBrute]? = some Sec2.thinBruteBody) :
    SolvesN thinTask P pAll (allInstancesTimeR R O) (allInstancesNeedR R O) := by
  refine ⟨allBody R.proc O.proc, hall, fun Q lim d x μ fr hpre hok => ?_⟩
  have ok : (allInstancesNeedR R O [x.N, x.D, x.w, x.U]).Ok lim fr d := hok
  have okO := allInstancesNeedR_ok ok
  have hword := ok.word
  have hcells := ok.cells
  have hdepth := ok.depth
  simp only [allInstancesNeedR] at hword hcells hdepth
  have hfits : ∀ n : ℕ, n ≤ R.word x.N x.D + (100 + x.D * (x.U * x.U)) → (n : ℤ) ≤ lim.word :=
    fun n hn => le_trans (by exact_mod_cast (by omega)) hword
  have h100 := hfits 100 (by omega)
  have hroom : fr + x.N + 1 ≤ lim.space := by omega
  clear hword hcells
  change Ends lim (P ++ Q) d (allBody R.proc O.proc)
    ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
    (R.time + 64 + if R.Reg x.N x.D then O.time x.N x.D x.w
      else 40 * ((x.w + 1) * (x.D + 1))) _
  unfold allBody
  refine Ends.callToThen (R.meets (R.aux_append P Q haux) (getElem?_append_of_eq_some htest Q)
    (by omega) x.N x.D hpre.N_pos hpre.D_pos (hfits _ (by omega)) μ) ?_ (hT := by simp; omega)
  rintro r μ ⟨rfl, hr⟩
  refine Ends.iteLast (fun hpos => ?_) (fun hneg => ?_)
  · have hreg : R.Reg x.N x.D := by
      rcases hr with ⟨-, h⟩ | ⟨rfl, -⟩
      · exact h
      · simp at hpos
    rw [if_pos hreg]
    exact Ends.callTo (O.meets (O.aux_append P Q hauxO) (getElem?_append_of_eq_some hoff Q) hpre
      (hfit _ _ hreg) okO) fun _ _ h => h
  · have hreg : ¬ R.Reg x.N x.D := by
      rcases hr with ⟨rfl, -⟩ | ⟨-, h⟩
      · simp at hneg
      · exact h
    rw [if_neg hreg]
    have hbrute : Meets lim (P ++ Q) Sec2.pThinBrute (d + 1)
        [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ (40 * ((x.w + 1) * (x.D + 1)))
        fun r μ' => thinTask.Post x μ fr r μ' :=
      .of_body (getElem?_append_of_eq_some hbrute Q) (Sec2.thinBrute_spec
        ⟨ok.space, by exact_mod_cast h100⟩ x μ fr (x.U : ℤ) hpre hroom (hfits _ (by omega)))
    exact Ends.callTo hbrute fun _ _ h => h

open Classical in
/-- The time of the solver is monotone in the number of wanted positions and does not depend on
the bound on the entries. -/
theorem allInstancesTimeR_mono (R : RegimeTest) (O : OfflineRoutine) (N D₀ : ℕ) {w w' : ℕ}
    (U U' : ℕ) (hw : w ≤ w') :
    allInstancesTimeR R O [N, D₀, w, U] ≤ allInstancesTimeR R O [N, D₀, w', U'] := by
  change R.time + 64 + (if R.Reg N D₀ then O.time N D₀ w else 40 * ((w + 1) * (D₀ + 1)))
    ≤ R.time + 64 + (if R.Reg N D₀ then O.time N D₀ w' else 40 * ((w' + 1) * (D₀ + 1)))
  split_ifs
  · have := O.time_mono N D₀ w w' hw
    omega
  · have := Nat.mul_le_mul_right (D₀ + 1) (show w + 1 ≤ w' + 1 by omega)
    omega

/-- The time of allInstances26 is monotone in the number of wanted positions and does not depend on
the bound on the entries. -/
theorem allInstancesTime_mono (G : RatParams) (N D₀ : ℕ) {w w' : ℕ} (U U' : ℕ) (hw : w ≤ w') :
    allInstancesTime G [N, D₀, w, U] ≤ allInstancesTime G [N, D₀, w', U'] :=
  allInstancesTimeR_mono regime18 (offline32Routine G) N D₀ U U' hw

/-- **The procedure allInstances26 of `program31 G` solves the task on all instances.** -/
theorem allInstances_program31 {G : RatParams} (hfit : Fits18 G) :
    SolvesN thinTask (program31 G) Proc.allInstances26 (allInstancesTime G)
      (allInstancesNeed G) :=
  allInstances_solves (R := regime18) (O := offline32Routine G) hfit
    (program31_at _ Proc.allInstances26) (program31_at _ Proc.regimeTest26) trivial
    (offline32Routine_program31 G).1 (offline32Routine_program31 G).2 (at_base58 rfl _)

/-! ## The need is polynomial in the parameters -/

/-- The need is polynomial in the parameters. The bounds on the need of the routine and on the
number the test forms go into the constant and the degree. -/
theorem allInstancesNeedR_poly (R : RegimeTest) (O : OfflineRoutine) :
    PolyNeedN (allInstancesNeedR R O) := by
  obtain ⟨kR, e, hwp⟩ := R.word_poly
  obtain ⟨s, k, hnp⟩ := O.need_poly
  refine ⟨9 + kR + s, 3 + e + k, fun ps => ?_⟩
  match ps with
  | [N, D, w, U] =>
    obtain ⟨hOw, hOc, hOd⟩ := hnp N D U
    have hRw := hwp N D
    have hND : (N + 1) * (D + 1) ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by positivity))
    have hNDU : (N + 1) * (D + 1) * (U + 1) ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega)))
    have hN : N + 1 ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have hD : D ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) :=
      calc D ≤ D + 1 := Nat.le_succ _
        _ ≤ (D + 1) * ((w + 1) * (U + 1)) := Nat.le_mul_of_pos_right _ (by positivity)
        _ ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) := Nat.le_mul_of_pos_left _ (by omega)
    have hU : U ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) :=
      calc U ≤ U + 1 := Nat.le_succ _
        _ ≤ (D + 1) * ((w + 1) * (U + 1)) :=
          Nat.le_mul_of_pos_left _ (by positivity) |>.trans
            (Nat.le_mul_of_pos_left _ (by positivity))
        _ ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) := Nat.le_mul_of_pos_left _ (by omega)
    rw [show polyBound (9 + kR + s) (3 + e + k) [N, D, w, U] =
      2 ^ (9 + kR + s) * ((N + 1) * ((D + 1) * ((w + 1) * (U + 1)))) ^ (3 + e + k) by
        simp [polyBound]]
    generalize (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) = Q at *
    have hQ : 1 ≤ Q := by omega
    have h3 : Q ^ 3 ≤ Q ^ (3 + e + k) := Nat.pow_le_pow_right hQ (by omega)
    -- the number the test forms
    have hRQ : R.word N D ≤ 2 ^ kR * Q ^ (3 + e + k) :=
      hRw.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hND e).trans
        (Nat.pow_le_pow_right hQ (by omega))))
    -- the need of the routine
    have hOQ : ∀ {n : ℕ}, n ≤ 2 ^ s * ((N + 1) * (D + 1) * (U + 1)) ^ k →
        n ≤ 2 ^ s * Q ^ (3 + e + k) :=
      fun h => h.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hNDU k).trans
        (Nat.pow_le_pow_right hQ (by omega))))
    have hOw' := hOQ hOw
    have hOc' := hOQ hOc
    have hOd' := hOQ hOd
    -- the brute force and the frame
    have hgen : 100 + D * (U * U) ≤ 101 * Q ^ (3 + e + k) := by
      have hDUU : D * (U * U) ≤ Q ^ 3 :=
        calc D * (U * U) ≤ Q * (Q * Q) := by gcongr
          _ = Q ^ 3 := by ring
      have h1 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ
      omega
    have hN1 : N + 1 ≤ Q ^ (3 + e + k) := hN.trans ((Nat.le_self_pow (by omega) Q).trans h3)
    have h1 : 1 ≤ Q ^ (3 + e + k) := Nat.one_le_pow _ _ hQ
    -- the three constants: 2^kR + 101 + 2^s ≤ 2^(9 + kR + s)
    have hpow : (2 : ℕ) ^ (9 + kR + s) * Q ^ (3 + e + k)
        = 512 * (2 ^ kR * 2 ^ s * Q ^ (3 + e + k)) := by
      rw [pow_add, pow_add]
      ring
    have hs1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have hkR1 : 1 ≤ 2 ^ kR := Nat.one_le_two_pow
    have hA : 2 ^ kR * Q ^ (3 + e + k) ≤ 2 ^ kR * 2 ^ s * Q ^ (3 + e + k) :=
      calc 2 ^ kR * Q ^ (3 + e + k) = 2 ^ kR * 1 * Q ^ (3 + e + k) := by ring
        _ ≤ 2 ^ kR * 2 ^ s * Q ^ (3 + e + k) := by gcongr
    have hB : 2 ^ s * Q ^ (3 + e + k) ≤ 2 ^ kR * 2 ^ s * Q ^ (3 + e + k) :=
      calc 2 ^ s * Q ^ (3 + e + k) = 1 * 2 ^ s * Q ^ (3 + e + k) := by ring
        _ ≤ 2 ^ kR * 2 ^ s * Q ^ (3 + e + k) := by gcongr
    have hC : Q ^ (3 + e + k) ≤ 2 ^ kR * 2 ^ s * Q ^ (3 + e + k) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    rw [hpow]
    refine ⟨?_, ?_, ?_⟩
    · change R.word N D + (100 + D * (U * U)) + (O.need N D U).word ≤ _
      omega
    · change N + 1 + (O.need N D U).cells ≤ _
      omega
    · change 2 + (O.need N D U).depth ≤ _
      omega
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ =>
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-- The need of allInstances26 is polynomial in the parameters. -/
theorem allInstancesNeed_poly (G : RatParams) : PolyNeedN (allInstancesNeed G) :=
  allInstancesNeedR_poly regime18 (offline32Routine G)

/-! ## The claim -/

/-- A routine that stays within its bounds does so with any constant added to its time: the bounds
are nonnegative, and already `400 ≤ A (…)`. -/
theorem OfflineWithinT.add_const {t : ℕ → ℕ → ℕ → ℕ} {ε γ q : ℝ} (h : OfflineWithinT t ε γ q)
    (K : ℕ) : ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      (t N D₀ w : ℝ) + 400 + K ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A * (1 + K / 400), fun N D₀ w hN hD hDN => ?_⟩
  have h := hA N D₀ w hN hD hDN
  have h0 : (0 : ℝ) ≤ t N D₀ w := by positivity
  have hK : (0 : ℝ) ≤ K := by positivity
  have hB : 400 ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀) := by linarith
  calc (t N D₀ w : ℝ) + 400 + K
      ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀)
        + K / 400 * (A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀)) := by
        have : K ≤ K / 400 * (A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀)) := by
          calc (K : ℝ) = K / 400 * 400 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
        linarith
    _ = A * (1 + K / 400) * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀) := by ring

/-- The offline routine stays within its bounds with any constant added to its time. -/
theorem OfflineWithin.add_const {G : RatParams} {ε γ q : ℝ} (h : OfflineWithin G ε γ q) (K : ℕ) :
    ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      (tOffline32 cShared30 G N D₀ w : ℝ) + 400 + K
        ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀) :=
  OfflineWithinT.add_const h K

/-- **The thin-product claim from an offline routine `O`, for a regime test `R`.** If the regime
lies where the routine is specified, the instances with `D ≤ N^ε` lie in the regime, and the
routine stays within its bounds there, then the thin product is solved within these bounds by the
procedure `pAll` of a program that holds the solver `allBody` with the test `R` and the routine
`O`, the test, the routine, the brute force and the procedures the test and the routine call. -/
theorem thinClaimR_of_offlineWithin {P : Program} {R : RegimeTest} {O : OfflineRoutine}
    {pAll : ℕ} {ε γ q : ℝ} (hfit : ∀ N D : ℕ, R.Reg N D → O.Ok N D)
    (hall : P[pAll]? = some (allBody R.proc O.proc)) (htest : P[R.proc]? = some R.body)
    (haux : R.aux P) (hoff : P[O.proc]? = some O.body) (hauxO : O.aux P)
    (hbrute : P[Sec2.pThinBrute]? = some Sec2.thinBruteBody)
    (hreg : ∀ N D₀ : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε → R.Reg N D₀)
    (h : OfflineWithinT O.time ε γ q) : ThinClaim lightModel ε γ q := by
  obtain ⟨A, hA⟩ := h.add_const (R.time + 64)
  refine ⟨A, fun N D₀ w _ => (allInstancesTimeR R O [N, D₀, w, 0] : ℝ),
    ⟨_, _, _, _, allInstancesNeedR_poly R O,
      allInstances_solves hfit hall htest haux hoff hauxO hbrute,
      fun N D₀ w w' U u _ _ _ hw _ => ?_⟩,
    fun N D₀ w u hN hD hDN => ?_⟩
  · change (allInstancesTimeR R O [N, D₀, w, U] : ℝ) ≤ (allInstancesTimeR R O [N, D₀, w', 0] : ℝ)
    exact_mod_cast allInstancesTimeR_mono R O N D₀ U 0 hw
  · have htime : (allInstancesTimeR R O [N, D₀, w, 0] : ℝ)
        = (O.time N D₀ w : ℝ) + 400 + ((R.time + 64 : ℕ) : ℝ) - 400 := by
      simp only [allInstancesTimeR, if_pos (hreg N D₀ hN hD hDN)]
      push_cast
      ring
    change (allInstancesTimeR R O [N, D₀, w, 0] : ℝ) ≤ _
    rw [htime]
    linarith [hA N D₀ w hN hD hDN]

/-- `D ≤ N^ε` with `ε ≤ s/r` puts the instance in the regime `D^r ≤ N^s`, for `1 ≤ r`. -/
theorem pow_le_pow_of_le_rpow {N D₀ r s : ℕ} {ε : ℝ} (hr : 1 ≤ r) (hε : ε ≤ (s : ℝ) / r)
    (hN : 1 ≤ N) (hDN : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : D₀ ^ r ≤ N ^ s := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h : ((D₀ : ℝ)) ^ r ≤ (N : ℝ) ^ s :=
    calc ((D₀ : ℝ)) ^ r ≤ ((N : ℝ) ^ ε) ^ r := pow_le_pow_left₀ (by positivity) hDN r
      _ = (N : ℝ) ^ (ε * r) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      _ ≤ (N : ℝ) ^ (s : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR
          (by rwa [le_div_iff₀ hrR] at hε)
      _ = (N : ℝ) ^ s := Real.rpow_natCast _ _
  exact_mod_cast h

/-- **The thin-product claim from the offline routine.** If the hypotheses of Theorem 30 hold at
`G` in the whole regime `D^18 ≤ N` (from the threshold on), the instances with `D ≤ N^ε` lie in the
regime (`ε ≤ 1/18`), and the offline routine stays within its bounds there, then the thin product is
solved within these bounds by a procedure of `program31 G`. -/
theorem thinClaim_of_offlineWithin {G : RatParams} {ε γ q : ℝ} (hfit : Fits18 G)
    (hε : ε ≤ 1 / 18) (h : OfflineWithin G ε γ q) :
    ThinClaim lightModel ε γ q :=
  thinClaimR_of_offlineWithin (R := regime18) (O := offline32Routine G) hfit
    (program31_at _ Proc.allInstances26) (program31_at _ Proc.regimeTest26) trivial
    (offline32Routine_program31 G).1 (offline32Routine_program31 G).2 (at_base58 rfl _)
    (fun N D₀ hN _ hDN => by
      have := pow_le_pow_of_le_rpow (r := 18) (s := 1) (by norm_num) (by simpa using hε) hN hDN
      exact (pow_one N).symm ▸ this)
    h

end ImprovedExponents
