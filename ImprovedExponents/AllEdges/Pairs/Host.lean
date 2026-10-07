module

public import ImprovedExponents.AllEdges.Pairs.Bridge
public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Passes
public import ThreeSumApsp.Lang.PolyBounded

@[expose] public section

/-!
# All pairs from all-edges Exact Triangle, as a host

Footnote 10 of the paper: the (min,+)-product reduces to all-edges Exact Triangle on the same `n`
vertices.  The threshold questions of upstream's `pairsTask` are answered, by Lemma F
(`ImprovedExponents.add_lt_iff_shiftDiff`), with `2b + 3` all-edges instances, `b = aeLevels U`.

pairsAE(n, U, x, y, v, out, fr) computes `b` and `2^b`, writes `X + U`, the transpose of `Y` plus
`U`, and `V + 2U` into an array r of `3n²` cells, zeros into an array q of `3n²` cells and into
out.  Then it makes `b` rounds: at the level `ℓ = b, …, 1` it asks, for `e = 2` and `e = 3`, the
all-edges instance with the third matrix `e − ⌊(V + 2U)/2^ℓ⌋` and takes the disjunction of the
answer into out (`or`), and then moves one more bit of every number from r to q (upstream's
`prefDown`).  At the level `0` it asks for `e = 2, 3, 1`.  The flags in out are then those of
`pairsTask` (`orFlags_eq_pairFlags`).

The text follows upstream's host from Negative Triangle to Exact Triangle
(`ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/Host.lean`); `isHost_pairsAE` is the
result.
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-! ## The text -/

namespace PairsHost

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The bound U on the entries. -/
abbrev Bound : ℕ := 1
/-- The address of X. -/
abbrev MatX : ℕ := 2
/-- The address of Y. -/
abbrev MatY : ℕ := 3
/-- The address of V. -/
abbrev MatV : ℕ := 4
/-- The address of the flags. -/
abbrev Out : ℕ := 5
/-- The free pointer, where the array q begins: the prefixes of X + U. -/
abbrev PreX : ℕ := 6
/-- n². -/
abbrev Cells : ℕ := 7
/-- 2^b. -/
abbrev Power : ℕ := 8
/-- The number b of levels. -/
abbrev Levels : ℕ := 9
/-- The number of the round. -/
abbrev Round : ℕ := 10
/-- The result of a call. -/
abbrev Res : ℕ := 11
/-- 3U. -/
abbrev Bound3 : ℕ := 12
/-- The prefixes of the transpose of Y plus U. -/
abbrev PreY : ℕ := 13
/-- The prefixes of V + 2U. -/
abbrev PreV : ℕ := 14
/-- The first part of the array r. -/
abbrev RestX : ℕ := 15
/-- The second part of the array r. -/
abbrev RestY : ℕ := 16
/-- The third part of the array r. -/
abbrev RestV : ℕ := 17
/-- The array for the third matrix of a question. -/
abbrev Third : ℕ := 18
/-- The array for the answer of a question. -/
abbrev Flg : ℕ := 19
/-- The free pointer for the solver. -/
abbrev SolverFree : ℕ := 20
/-- 3n². -/
abbrev Cells3 : ℕ := 21
/-- 9U. -/
abbrev Bound9 : ℕ := 22

end PairsHost

open PairsHost

/-- The beginning of pairsAE: sizes and addresses. -/
def paInit : Stmt :=
  .set Cells (v Verts *' v Verts) ;;
  .set Bound3 (k 3 *' v Bound) ;;
  .set Bound9 (k 9 *' v Bound) ;;
  .set PreY (v PreX +' v Cells) ;;
  .set PreV (v PreY +' v Cells) ;;
  .set RestX (v PreV +' v Cells) ;;
  .set RestY (v RestX +' v Cells) ;;
  .set RestV (v RestY +' v Cells) ;;
  .set Third (v RestV +' v Cells) ;;
  .set Flg (v Third +' v Cells) ;;
  .set SolverFree (v Flg +' v Cells) ;;
  .set Cells3 (k 3 *' v Cells) ;;
  .set Power (k 1) ;;
  .set Levels (k 0)

/-- The number of levels b and the power 2^b, by doubling. -/
def paPow : Stmt :=
  .while (v Power ≤' v Bound3) (
    .set Power (k 2 *' v Power) ;;
    .set Levels (v Levels +' k 1))

/-- The arrays r and q at the top level, and zeros in out. -/
def paFill (pAff pTr : ℕ) : Stmt :=
  .call pAff [v Cells, v MatX, k 1, v Bound, v RestX] Res ;;
  .call pTr [v Verts, v MatY, v Bound, v RestY] Res ;;
  .call pAff [v Cells, v MatV, k 1, k 2 *' v Bound, v RestV] Res ;;
  .call pAff [v Cells3, v RestX, k 0, k 0, v PreX] Res ;;
  .call pAff [v Cells, v MatX, k 0, k 0, v Out] Res

/-- One question to the solver of all-edges Exact Triangle: the third matrix for the value e, the
call, and the disjunction of the answer into out. -/
def paProbe (pAE pAff pOr e : ℕ) : Stmt :=
  .call pAff [v Cells, v PreV, k 0 -' k 1, k e, v Third] Res ;;
  .call pAE [v Verts, v Bound9, v Third, v PreY, v PreX, v Flg, v SolverFree] Res ;;
  .call pOr [v Cells, v Flg, v Out] Res

/-- One round: the two questions at the level, then the next level. -/
def paRound (pAE pAff pOr pDown : ℕ) : Stmt :=
  paProbe pAE pAff pOr 2 ;; paProbe pAE pAff pOr 3 ;;
  .call pDown [v Cells3, v PreX, v RestX, v Power] Res

/-- pairsAE(n, U, x, y, v, out, fr). -/
def paBody (pAE pAff pTr pOr pDown : ℕ) : Stmt :=
  paInit ;; paPow ;; paFill pAff pTr ;; .for Round (v Levels) (paRound pAE pAff pOr pDown) ;;
  paProbe pAE pAff pOr 2 ;; paProbe pAE pAff pOr 3 ;; paProbe pAE pAff pOr 1 ;; .set 0 (k 0)

/-- The time of pairsAE, if the solver of all-edges Exact Triangle takes T n U steps: `2b + 3`
calls of the solver, each with O(n²) work around it, and O(n²) work at the start. -/
def pairsTimeAE (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  (2 * aeLevels U + 3) * (T n (9 * U) + 108 * (n * n) + 60) + 200 * (n * n) + 150

/-- The need of pairsAE, if the solver needs r n U. -/
def pairsNeedAE (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := 24 * U + 8 + (r n (9 * U)).word
  cells := 8 * (n * n) + (r n (9 * U)).cells
  depth := (r n (9 * U)).depth + 1

/-! ## The local variables and the hypotheses -/

namespace PairsHost

/-- The locals of pairsAE after its beginning; the last four are those that change later. -/
abbrev locals (x : PairsInst) (fr : ℕ) (pw lv rd res : ℤ) : List ℤ :=
  [x.n, x.U, x.x, x.y, x.v, x.out, fr, (x.n * x.n : ℕ), pw, lv, rd, res, (3 * x.U : ℕ),
    (fr + x.n * x.n : ℕ), (fr + 2 * (x.n * x.n) : ℕ), (fr + 3 * (x.n * x.n) : ℕ),
    (fr + 4 * (x.n * x.n) : ℕ), (fr + 5 * (x.n * x.n) : ℕ), (fr + 6 * (x.n * x.n) : ℕ),
    (fr + 7 * (x.n * x.n) : ℕ), (fr + 8 * (x.n * x.n) : ℕ), (3 * (x.n * x.n) : ℕ), (9 * x.U : ℕ)]

/-- The program has the solver and the four loops over arrays, the instance is as the task
prescribes, and the limits allow for the need of pairsAE. -/
structure Ctx (P₀ R' : Program) (p pAff pTr pOr pDown : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (lim : Limits) (d : ℕ) (x : PairsInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  solver : Solves aeTask P₀ p T r
  aff : (P₀ ++ R')[pAff]? = some affineBody
  tr : (P₀ ++ R')[pTr]? = some transposeBody
  orp : (P₀ ++ R')[pOr]? = some orBody
  down : (P₀ ++ R')[pDown]? = some prefDownBody
  pre : x.Pre μ fr
  ok : (pairsNeedAE r x.n x.U).Ok lim fr d

variable {P₀ R' : Program} {p pAff pTr pOr pDown : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {lim : Limits} {d : ℕ} {x : PairsInst} {μ : ℕ → ℤ} {fr : ℕ}

/-- The start list of the instance. -/
abbrev Z (x : PairsInst) : List ℤ := pStart x.n x.U x.X x.Y x.V

/-- The flag of the instance `c` at the cell `q`. -/
def hit (x : PairsInst) (c : ℕ × ℤ) (q : ℕ) : Prop :=
  (aeFlags x.n (instAB x.U x.V c.1 c.2) (instBC x.n x.U x.Y c.1) (instAC x.U x.X c.1)).getD q 0 = 1

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/Host.lean
/-- The arithmetic facts of the hypotheses as one conjunction. -/
private theorem Ctx.places (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    ((lim.space : ℤ) ≤ lim.word ∧ 24 * (x.U : ℤ) + 8 + (r x.n (9 * x.U)).word ≤ lim.word ∧
      fr + (8 * (x.n * x.n) + (r x.n (9 * x.U)).cells) ≤ lim.space ∧
      d + ((r x.n (9 * x.U)).depth + 1) ≤ lim.depth) ∧ 1 ≤ x.n * x.n ∧ 1 ≤ x.U ∧
      (x.X.length = x.n * x.n ∧ x.Y.length = x.n * x.n ∧ x.V.length = x.n * x.n) ∧
      x.x + x.n * x.n ≤ fr ∧ x.y + x.n * x.n ≤ fr ∧ x.v + x.n * x.n ≤ fr ∧
      x.out + x.n * x.n ≤ fr ∧ (Z x).length = 3 * (x.n * x.n) ∧
      3 * x.U < 2 ^ aeLevels x.U ∧ 2 ^ aeLevels x.U ≤ 6 * x.U :=
  ⟨⟨C.ok.space, by exact_mod_cast C.ok.word, C.ok.cells, C.ok.depth⟩,
    Nat.mul_pos C.pre.n_pos C.pre.n_pos, C.pre.U_pos, ⟨C.pre.lenX, C.pre.lenY, C.pre.lenV⟩,
    C.pre.belowX, C.pre.belowY, C.pre.belowV, C.pre.belowOut,
    length_pStart C.pre.lenX C.pre.lenV, lt_two_pow_aeLevels _,
    two_pow_aeLevels_le C.pre.U_pos⟩

/-- **affine** as a procedure, for a source and a destination that lie apart, below the free pointer
of the solver. -/
private theorem Ctx.affine_meets (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {μ' : ℕ → ℤ}
    {l : List ℤ} {src dst : ℕ} {m c : ℤ} (hl : Seg μ' src l)
    (hplace : src + l.length ≤ fr + 8 * (x.n * x.n) ∧ dst + l.length ≤ fr + 8 * (x.n * x.n) ∧
      (src + l.length ≤ dst ∨ dst + l.length ≤ src))
    (hfits : ∀ w ∈ l, |m * w| ≤ lim.word ∧ |m * w + c| ≤ lim.word) :
    Meets lim (P₀ ++ R') pAff (d + 1) [l.length, src, m, c, dst] μ' (20 * l.length + 6)
      fun _ μ'' => Seg μ'' dst (affL m c l) ∧ SameOutside μ' μ'' dst l.length := by
  have hplaces := C.places
  exact Sec3.affine_meets C.aff hl C.ok.space (by omega) (by omega) hplace.2.2 hfits

/-! ## The beginning -/

/-- **The beginning** sets the sizes and the addresses. -/
private theorem init_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d paInit ⟨frame [x.n, x.U, x.x, x.y, x.v, x.out, fr], μ⟩ paInit.blockCost
      fun σ' => σ' = ⟨frame (locals x fr 1 0 0 0), μ⟩ := by
  have hplaces := C.places
  have hsquare : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
  unfold paInit
  light_set (x.n * x.n : ℕ)
  light_set (3 * x.U : ℕ)
  light_set (9 * x.U : ℕ)
  light_set (fr + x.n * x.n : ℕ)
  light_set (fr + 2 * (x.n * x.n) : ℕ)
  light_set (fr + 3 * (x.n * x.n) : ℕ)
  light_set (fr + 4 * (x.n * x.n) : ℕ)
  light_set (fr + 5 * (x.n * x.n) : ℕ)
  light_set (fr + 6 * (x.n * x.n) : ℕ)
  light_set (fr + 7 * (x.n * x.n) : ℕ)
  light_set (fr + 8 * (x.n * x.n) : ℕ)
  light_set (3 * (x.n * x.n) : ℕ)
  light_set 1
  light_set 0
  rfl

/-- The state of the loop that doubles after i rounds. -/
def PowInv (x : PairsInst) (μ : ℕ → ℤ) (fr i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame (locals x fr (2 ^ i : ℕ) i 0 0), μ⟩

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/Host.lean
/-- **The loop that doubles** computes the number b of levels and 2^b. -/
private theorem pow_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d paPow ⟨frame (locals x fr 1 0 0 0), μ⟩ (14 * aeLevels x.U + 6)
      fun σ' => σ' = ⟨frame (locals x fr (2 ^ aeLevels x.U : ℕ) (aeLevels x.U) 0 0), μ⟩ := by
  have hplaces := C.places
  refine Ends.whileBlock (PowInv x μ fr) (aeLevels x.U) (by simp [PowInv]) ?round ?done
    (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hpow : 2 ^ (i + 1) ≤ 2 ^ aeLevels x.U := Nat.pow_le_pow_right (by norm_num) hi
    have hlt : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
    rw [pow_succ'] at hpow hlt
    generalize hpw : 2 ^ i = pw at hpow hlt ⊢
    exact ⟨by light_side, by simp; omega, by light_side,
      by simp [PowInv, pow_succ', hpw, update_frame_setLocal, locals]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ aeLevels x.U = pw at hplaces ⊢
    exact ⟨by light_side, by simp; omega, rfl⟩

/-! ## The memory -/

/-- The memory at the level ℓ with the asked set S: q holds the prefixes, r the rests, out the
disjunction of the flags of the instances in S, and nothing else below the free pointer changed. -/
def PMem (x : PairsInst) (μ : ℕ → ℤ) (fr ℓ : ℕ) (S : ℕ × ℤ → Prop) (μ' : ℕ → ℤ) : Prop :=
  Seg μ' fr ((Z x).map (prefQ ℓ)) ∧
    Seg μ' (fr + 3 * (x.n * x.n)) ((Z x).map (prefR (aeLevels x.U) ℓ)) ∧
    Seg μ' x.out (orFlags (x.n * x.n) S (hit x)) ∧ KeptBut μ μ' fr x.out (x.n * x.n)

/-- The numbers in the array r at the top level lie in `[0, 3U]`, below `2^b`. -/
private theorem Z_range (hpre : x.Pre μ fr) :
    ∀ z ∈ Z x, 0 ≤ z ∧ z ≤ 3 * (x.U : ℤ) ∧ z < 2 ^ aeLevels x.U := by
  intro z hz
  obtain ⟨h0, h1⟩ := pStart_range hpre.leX hpre.leY hpre.leV hpre.lenY z hz
  have h2 : ((3 * x.U : ℕ) : ℤ) < ((2 ^ aeLevels x.U : ℕ) : ℤ) := by
    exact_mod_cast lt_two_pow_aeLevels x.U
  push_cast at h2
  exact ⟨h0, h1, by omega⟩

/-- The three parts of the array q. -/
private theorem seg_parts (hpre : x.Pre μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ}
    (hq : Seg μ' fr ((Z x).map (prefQ ℓ))) :
    Seg μ' fr (instAC x.U x.X ℓ) ∧ Seg μ' (fr + x.n * x.n) (instBC x.n x.U x.Y ℓ) ∧
      Seg μ' (fr + 2 * (x.n * x.n)) ((affL 1 (2 * x.U) x.V).map (prefQ ℓ)) := by
  simp only [Z, pStart, List.map_append] at hq
  rw [seg_append, seg_append] at hq
  simp only [List.length_map, length_affL, length_transposeL, hpre.lenX] at hq
  rwa [show fr + x.n * x.n + x.n * x.n = fr + 2 * (x.n * x.n) by omega] at hq

/-- **The five calls** fill the arrays r and q for the top level and zero out. -/
private theorem fill_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) (pw lv rd res : ℤ) :
    Ends lim (P₀ ++ R') d (paFill pAff pTr) ⟨frame (locals x fr pw lv rd res), μ⟩
      (170 * (x.n * x.n) + 70) fun σ' => ∃ res' μ',
        σ' = ⟨frame (locals x fr pw lv rd res'), μ'⟩ ∧
          PMem x μ fr (aeLevels x.U) (fun _ => False) μ' := by
  have hpre := C.pre
  have hplaces := C.places
  have hZ := Z_range hpre
  have hn : x.n ≤ x.n * x.n := Nat.le_mul_self x.n
  have hapX := hpre.apartX
  have hW : 24 * (x.U : ℤ) + 8 ≤ lim.word := by omega
  have hfit1 : ∀ c : ℤ, c = x.U ∨ c = 2 * x.U → ∀ w ∈ x.V ++ x.X, |1 * w| ≤ lim.word ∧
      |1 * w + c| ≤ lim.word := fun c hc w hw => by
    have := abs_le.1 ((List.mem_append.1 hw).elim (hpre.leV w) (hpre.leX w))
    simp only [one_mul, abs_le]
    rcases hc with rfl | rfl <;> omega
  unfold paFill
  -- Res := pAff(Cells, MatX, 1, Bound, RestX)
  refine Ends.callToThen (C.affine_meets (m := 1) (c := x.U) (dst := fr + 3 * (x.n * x.n))
    hpre.segX (by omega) fun w hw => hfit1 _ (Or.inl rfl) w (by simp [hw])) ?_
    (ha := by light_side [hpre.lenX]) (hT := by simp [hpre.lenX]; omega)
  rintro r₁ μ₁ ⟨s₁, o₁⟩
  -- Res := pTr(Verts, MatY, Bound, RestY)
  refine Ends.callToThen (transpose_meets C.tr (dst := fr + 4 * (x.n * x.n)) (c := x.U)
    hpre.segY.keep hpre.lenY (by omega) ⟨C.ok.space, by omega, by omega⟩ fun w hw => by
      have := abs_le.1 (hpre.leY w hw); rw [abs_le]; omega) ?_
    (ha := by light_side) (hT := by simp [hpre.lenX]; omega)
  rintro r₂ μ₂ ⟨s₂, o₂⟩
  -- Res := pAff(Cells, MatV, 1, 2 * Bound, RestV)
  refine Ends.callToThen (C.affine_meets (m := 1) (c := 2 * x.U) (dst := fr + 5 * (x.n * x.n))
    hpre.segV.keep (by omega) fun w hw => hfit1 _ (Or.inr rfl) w (by simp [hw])) ?_
    (ha := by light_side [hpre.lenV]) (hT := by simp [hpre.lenX, hpre.lenV]; omega)
  rintro r₃ μ₃ ⟨s₃, o₃⟩
  have sZ : Seg μ₃ (fr + 3 * (x.n * x.n)) (Z x) := by
    rw [Z, pStart, seg_append, seg_append]
    simp only [length_affL, length_transposeL, hpre.lenX]
    rw [show fr + 3 * (x.n * x.n) + x.n * x.n = fr + 4 * (x.n * x.n) by omega,
      show fr + 4 * (x.n * x.n) + x.n * x.n = fr + 5 * (x.n * x.n) by omega]
    exact ⟨s₁.keep, s₂.keep, s₃⟩
  -- Res := pAff(Cells3, RestX, 0, 0, PreX)
  refine Ends.callToThen (C.affine_meets (m := 0) (c := 0) (dst := fr) sZ (by omega)
    fun w _ => by simp; omega) ?_ (ha := by light_side) (hT := by simp; omega)
  rintro r₄ μ₄ ⟨s₄, o₄⟩
  -- Res := pAff(Cells, MatX, 0, 0, Out)
  refine Ends.callTo (C.affine_meets (m := 0) (c := 0) (dst := x.out) hpre.segX.keep (by omega)
    fun w _ => by simp; omega) ?_ (ha := by light_side [hpre.lenX])
    (hT := by simp [hpre.lenX]; omega)
  rintro r₅ μ₅ ⟨s₅, o₅⟩
  refine ⟨r₅, μ₅, rfl, ?_, ?_, ?_, fun c hc => ?_⟩
  · rw [map_prefQ_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]
    exact s₄.keep
  · rw [map_prefR_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]
    exact sZ.keep
  · rw [orFlags_false _ _ hpre.lenX]
    exact s₅
  · light_keep

/-! ## One question -/

/-- The instance of all-edges Exact Triangle for the level ℓ and the value e, as it lies in the
arrays. -/
def question (x : PairsInst) (fr ℓ : ℕ) (e : ℤ) : AeInst :=
  ⟨x.n, 9 * x.U, fr + 6 * (x.n * x.n), fr + x.n * x.n, fr, fr + 7 * (x.n * x.n),
    instAB x.U x.V ℓ e, instBC x.n x.U x.Y ℓ, instAC x.U x.X ℓ⟩

/-- The question is an instance as the task prescribes. -/
private theorem question_pre (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {μ' : ℕ → ℤ}
    {ℓ : ℕ} {e : ℤ} (he : 1 ≤ e ∧ e ≤ 3) (hq : Seg μ' fr ((Z x).map (prefQ ℓ)))
    (hthird : Seg μ' (fr + 6 * (x.n * x.n)) (instAB x.U x.V ℓ e)) :
    (question x fr ℓ e).Pre μ' (fr + 8 * (x.n * x.n)) := by
  have hpre := C.pre
  have hplaces := C.places
  obtain ⟨hqX, hqY, -⟩ := seg_parts hpre hq
  obtain ⟨b1, b2, b3⟩ := absLe_inst hpre.leX hpre.leY hpre.leV hpre.lenY hpre.U_pos (ℓ := ℓ) he
  exact {
    n_pos := hpre.n_pos
    U_pos := by simp only [question]; omega
    lenAB := by simp [question, instAB, hpre.lenV]
    lenBC := by simp [question, instBC]
    lenAC := by simp [question, instAC, hpre.lenX]
    segAB := hthird
    segBC := hqY
    segAC := hqX
    leAB := b1
    leBC := b2
    leAC := b3
    belowAB := by simp only [question]; omega
    belowBC := by simp only [question]; omega
    belowAC := by simp only [question]; omega
    belowOut := by simp only [question]; omega
    apartAB := by simp only [question]; omega
    apartBC := by simp only [question]; omega
    apartAC := by simp only [question]; omega }

/-- The state between two steps: the locals, with some result of the last call, and the memory at
the level ℓ with the asked set S. -/
def St (x : PairsInst) (μ : ℕ → ℤ) (fr : ℕ) (rd : ℤ) (ℓ : ℕ) (S : ℕ × ℤ → Prop) (σ : State) :
    Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals x fr (2 ^ aeLevels x.U : ℕ) (aeLevels x.U) rd res), μ'⟩ ∧
      PMem x μ fr ℓ S μ'

/-- The time of one question. -/
abbrev probeTime (T : ℕ → ℕ → ℕ) (x : PairsInst) : ℕ := 51 * (x.n * x.n) + 35 + T x.n (9 * x.U)

/-- The flags of the solver are 0 or 1. -/
private theorem aeFlags_01 (n : ℕ) (AB BC AC : List ℤ) :
    ∀ f ∈ aeFlags n AB BC AC, f = 0 ∨ f = 1 := by
  intro f hf
  simp only [aeFlags, List.mem_map] at hf
  obtain ⟨q, -, rfl⟩ := hf
  unfold flag
  split_ifs <;> simp

/-- The flag of the instance `(ℓ, e)`, spelled out. -/
private theorem hit_iff (x : PairsInst) (ℓ : ℕ) (e : ℤ) (q : ℕ) :
    hit x (ℓ, e) q ↔
      (aeFlags x.n (instAB x.U x.V ℓ e) (instBC x.n x.U x.Y ℓ) (instAC x.U x.X ℓ)).getD q 0 = 1 :=
  Iff.rfl

/-- **One question** leaves the arrays as they are and adds the instance `(ℓ, e)` to the asked set.
-/
private theorem probe_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {ℓ e : ℕ}
    (he : 1 ≤ e ∧ e ≤ 3) {rd : ℤ} {S : ℕ × ℤ → Prop} {σ : State} (hσ : St x μ fr rd ℓ S σ) :
    Ends lim (P₀ ++ R') d (paProbe p pAff pOr e) σ (probeTime T x)
      (St x μ fr rd ℓ (fun c => S c ∨ c = (ℓ, (e : ℤ)))) := by
  obtain ⟨res, μ₀, rfl, hq, hr, hout, hk⟩ := hσ
  have hpre := C.pre
  have hplaces := C.places
  have he' : 1 ≤ (e : ℤ) ∧ (e : ℤ) ≤ 3 := by omega
  have hlenV : ((affL 1 (2 * x.U) x.V).map (prefQ ℓ)).length = x.n * x.n := by simp [hpre.lenV]
  have hV3 := (absLe_pStart_parts hpre.leX hpre.leY hpre.leV hpre.lenY ℓ).2.2
  have h01 := aeFlags_01 x.n (instAB x.U x.V ℓ e) (instBC x.n x.U x.Y ℓ) (instAC x.U x.X ℓ)
  unfold paProbe
  -- Res := pAff(Cells, PreV, 0 - 1, e, Third)
  refine Ends.callToThen (C.affine_meets (m := -1) (c := e) (dst := fr + 6 * (x.n * x.n))
    (seg_parts hpre hq).2.2 (by omega) fun w hw => ?_) ?_
    (ha := by light_side [hlenV]) (hT := by simp [hlenV, probeTime]; omega)
  · have := hV3 w hw
    simp only [abs_le]
    omega
  rintro r₁ μ₁ ⟨hthird, h₁⟩
  rw [hlenV] at h₁
  have hq₁ : Seg μ₁ fr ((Z x).map (prefQ ℓ)) := hq.keep (by light_keep)
  -- Res := pAE(Verts, Bound9, Third, PreY, PreX, Flg, SolverFree)
  refine Ends.callToThen (C.solver.meets R' (question x fr ℓ e) (fr + 8 * (x.n * x.n))
    (question_pre C he' hq₁ hthird)
    { word := by simp only [aeTask, question]; omega
      cells := by simp only [aeTask, question]; omega
      space := C.ok.space
      depth := by simp only [aeTask, question]; omega }) ?_ (by simp [aeTask, question])
    (hT := by simp [aeTask, question, probeTime]; omega)
  rintro r₂ μ₂ ⟨hflg, h₂⟩
  simp only [question] at hflg h₂
  have hout₂ : Seg μ₂ x.out (orFlags (x.n * x.n) S (hit x)) :=
    hout.keep (by light_keep)
  -- Res := pOr(Cells, Flg, Out)
  refine Ends.callTo (or_meets C.orp (len := x.n * x.n) hflg hout₂ (by simp) (by omega)
    ⟨C.ok.space, by omega, by omega⟩ h01 (orFlags_mem _ _ _) (by omega)) ?_
    (ha := by light_side) (hT := by simp [aeTask, question, probeTime]; omega)
  rintro r₃ μ₃ ⟨hout₃, h₃⟩
  have hor := orL_orFlags (S := S) (c := (ℓ, (e : ℤ))) (length_aeFlags x.n _ _ _)
    (fun q _ => hit_iff x ℓ e q) h01
  rw [hor] at hout₃
  exact ⟨r₃, μ₃, rfl, hq₁.keep (by light_keep), hr.keep (by light_keep), hout₃,
    fun c hc => by light_keep⟩

/-! ## The rounds -/

/-- What prefDown needs holds at every level above 0. -/
private theorem down_pre (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ aeLevels x.U) (hq : Seg μ' fr ((Z x).map (prefQ (ℓ + 1))))
    (hr : Seg μ' (fr + 3 * (x.n * x.n)) ((Z x).map (prefR (aeLevels x.U) (ℓ + 1)))) :
    PrefPre lim μ' fr (fr + 3 * (x.n * x.n)) (2 ^ aeLevels x.U)
      ((Z x).map (prefQ (ℓ + 1))) ((Z x).map (prefR (aeLevels x.U) (ℓ + 1))) := by
  have hplaces := C.places
  have hZ := Z_range C.pre
  have hL : ((2 ^ aeLevels x.U : ℕ) : ℤ) ≤ ((6 * x.U : ℕ) : ℤ) := by
    exact_mod_cast two_pow_aeLevels_le C.pre.U_pos
  push_cast at hL
  refine ⟨hq, hr, by simp, C.ok.space, by simp; omega, by simp; omega, by simp; omega, by omega,
    fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have h0 := prefQ_nonneg (hZ z hz).1 (ℓ + 1)
    have h1 := (prefQ_le (hZ z hz).1 (ℓ + 1)).trans (hZ z hz).2.1
    simp only [abs_le]
    omega
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have h0 := prefR_nonneg (aeLevels x.U) (ℓ + 1) z
    have h1 := prefR_lt hℓ z
    simp only [abs_le]
    omega

/-- The time of one round. -/
abbrev roundTime (T : ℕ → ℕ → ℕ) (x : PairsInst) : ℕ := 2 * probeTime T x + 114 * (x.n * x.n) + 12

/-- **One round** at the level ℓ + 1: the two questions, then the level ℓ. -/
private theorem round_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ aeLevels x.U) {rd : ℤ} {σ : State}
    (hσ : St x μ fr rd (ℓ + 1) (Above (ℓ + 1) (aeLevels x.U)) σ) :
    Ends lim (P₀ ++ R') d (paRound p pAff pOr pDown) σ (roundTime T x)
      (St x μ fr rd ℓ (Above ℓ (aeLevels x.U))) := by
  have hplaces := C.places
  have hZl : (Z x).length = 3 * (x.n * x.n) := length_pStart C.pre.lenX C.pre.lenV
  unfold paRound
  refine Ends.next _ ((probe_spec C (by norm_num) hσ).mono le_rfl fun σ₂ hσ₂ => ?_)
    (by simp only [roundTime, probeTime]; omega)
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₂).mono le_rfl fun σ₃ hσ₃ => ?_)
    (by simp only [roundTime, probeTime]; omega)
  obtain ⟨res, μ₀, rfl, hq, hr, hout, hk⟩ := hσ₃
  -- Res := pDown(Cells3, PreX, RestX, Power)
  refine Ends.callTo (prefDown_meets C.down (down_pre C hℓ hq hr)) ?_ (by simp [hZl])
    (hT := by simp [roundTime, probeTime]; omega)
  rintro r₁ μ₁ ⟨hq', hr', hrest⟩
  rw [zipWith_shiftQ hℓ] at hq'
  rw [map_shiftR hℓ] at hr'
  simp only [List.length_map] at hrest
  refine ⟨r₁, μ₁, rfl, hq', hr', ?_, fun c hc => ?_⟩
  · have : orFlags (x.n * x.n) (fun c => (Above (ℓ + 1) (aeLevels x.U) c ∨ c = (ℓ + 1, 2)) ∨
        c = (ℓ + 1, 3)) (hit x) = orFlags (x.n * x.n) (Above ℓ (aeLevels x.U)) (hit x) := by
      simp only [orFlags]
      exact List.map_congr_left fun q _ => flag_congr (exists_congr fun c =>
        and_congr_left fun _ => above_step hℓ c)
    rw [← this]
    refine hout.keep fun a ha => ?_
    rw [length_orFlags] at ha
    exact hrest a (Or.inl (by omega)) (Or.inl (by omega))
  · exact (hrest c (Or.inl (by omega)) (Or.inl (by omega))).trans (hk c hc)

/-- **The b rounds**: from the level b to the level 0. -/
private theorem rounds_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {res : ℤ}
    {μ' : ℕ → ℤ} (hm : PMem x μ fr (aeLevels x.U) (fun _ => False) μ') :
    Ends lim (P₀ ++ R') d (.for Round (v Levels) (paRound p pAff pOr pDown))
      ⟨frame (locals x fr (2 ^ aeLevels x.U : ℕ) (aeLevels x.U) 0 res), μ'⟩
      (aeLevels x.U * (roundTime T x + 8) + 6)
      (St x μ fr (aeLevels x.U) 0 (Above 0 (aeLevels x.U))) := by
  have hplaces := C.places
  have hL : aeLevels x.U ≤ 6 * x.U :=
    (Nat.lt_two_pow_self (n := aeLevels x.U)).le.trans (two_pow_aeLevels_le C.pre.U_pos)
  refine Ends.for (fun t σ => St x μ fr t (aeLevels x.U - t) (Above (aeLevels x.U - t)
    (aeLevels x.U)) σ) (aeLevels x.U) (roundTime T x) ?start ?round ?done ?bound (by omega)
    (by simp; ring_nf; omega)
  case start =>
    refine ⟨res, μ', ?_, ?_⟩
    · rw [update_frame_setLocal]
      rfl
    · simp only [Nat.sub_zero]
      have : orFlags (x.n * x.n) (Above (aeLevels x.U) (aeLevels x.U)) (hit x) =
          orFlags (x.n * x.n) (fun _ => False) (hit x) := by
        simp only [orFlags]
        exact List.map_congr_left fun q _ => flag_congr (exists_congr fun c =>
          and_congr_left fun _ => iff_of_false (above_self _ c) id)
      obtain ⟨h1, h2, h3, h4⟩ := hm
      exact ⟨h1, h2, this ▸ h3, h4⟩
  case round =>
    intro t σ ht _ hσ
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, aeLevels x.U - t = ℓ + 1 := ⟨aeLevels x.U - t - 1, by omega⟩
    rw [show aeLevels x.U - (t + 1) = ℓ by omega]
    rw [hℓ] at hσ
    refine (round_spec C (by omega) hσ).mono le_rfl fun σ' hσ' => ?_
    obtain ⟨res', μ'', rfl, hm'⟩ := hσ'
    exact ⟨rfl, res', μ'', by rw [update_frame_setLocal]; rfl, hm'⟩
  case done =>
    intro σ _ hσ
    simpa using hσ
  case bound =>
    rintro t _ - - ⟨res', μ'', rfl, -⟩
    exact ⟨trivial, rfl⟩

/-! ## The procedure -/

/-- **pairsAE is correct**, in every program that begins with the solver's program and has the four
loops over arrays. -/
theorem pairsAE_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d (paBody p pAff pTr pOr pDown)
      ⟨frame [x.n, x.U, x.x, x.y, x.v, x.out, fr], μ⟩ (pairsTimeAE T x.n x.U) fun σ' =>
        Seg σ'.mem x.out (pairFlags x.n x.X x.Y x.V) ∧ KeptBut μ σ'.mem fr x.out (x.n * x.n) := by
  have hpre := C.pre
  have hplaces := C.places
  have htime : pairsTimeAE T x.n x.U = aeLevels x.U * (roundTime T x + 8) + 6 +
      (3 * probeTime T x + 30 * aeLevels x.U + 371 * (x.n * x.n) + 219) := by
    simp only [pairsTimeAE, roundTime, probeTime]
    ring
  rw [htime]
  unfold paBody
  -- paInit
  refine Ends.next _ ((init_spec C).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ rfl
  -- paPow
  refine Ends.next _ ((pow_spec C).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ rfl
  -- paFill
  refine Ends.next _ ((fill_spec C _ _ _ _).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ ⟨res, μ₁, rfl, hm⟩
  -- the rounds
  refine Ends.next _ ((rounds_spec C hm).mono le_rfl ?_) (by simp [paInit]; omega)
  intro σ₂ hσ₂
  -- the three questions at the level 0
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₂).mono le_rfl fun σ₃ hσ₃ => ?_)
    (by simp [paInit]; omega)
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₃).mono le_rfl fun σ₄ hσ₄ => ?_)
    (by simp [paInit]; omega)
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₄).mono le_rfl fun σ₅ hσ₅ => ?_)
    (by simp [paInit]; omega)
  obtain ⟨res', μ₅, rfl, -, -, hout, hk⟩ := hσ₅
  refine Ends.setTo 0 ⟨?_, hk⟩ (hT := by simp [paInit]; omega)
  rw [← orFlags_eq_pairFlags hpre.leX hpre.leY hpre.leV hpre.lenX hpre.lenY hpre.lenV]
  have : orFlags (x.n * x.n) (fun c => ((Above 0 (aeLevels x.U) c ∨ c = (0, ((2 : ℕ) : ℤ))) ∨
      c = (0, ((3 : ℕ) : ℤ))) ∨ c = (0, ((1 : ℕ) : ℤ))) (hit x) =
      orFlags (x.n * x.n) (fun c => c ∈ lemmaFInstances (aeLevels x.U)) (hit x) := by
    simp only [orFlags]
    exact List.map_congr_left fun q _ => flag_congr (exists_congr fun c =>
      and_congr_left fun _ => by push_cast; exact above_zero_iff _ c)
  exact this ▸ hout

end PairsHost

/-- The need of pairsAE is polynomially bounded if the need of the solver is. -/
theorem polyNeed_pairsNeedAE {r : ℕ → ℕ → Need} (h : PolyNeed r) : PolyNeed (pairsNeedAE r) := by
  unfold pairsNeedAE
  poly_need [h.word, h.cells, h.depth]

/-- **All pairs from all-edges Exact Triangle**: from every solver of all-edges Exact Triangle, the
five procedures affine, transpose, or, prefDown, pairsAE make a solver of all pairs. -/
theorem isHost_pairsAE : IsHost aeTask pairsTask pairsTimeAE pairsNeedAE := by
  refine ⟨fun P p T r hsol => ⟨[affineBody, transposeBody, orBody, prefDownBody,
    paBody p P.length (P.length + 1) (P.length + 2) (P.length + 3)], P.length + 4,
    paBody p P.length (P.length + 1) (P.length + 2) (P.length + 3), by simp,
    fun R lim d x μ fr hpre hok => ?_⟩, fun r => polyNeed_pairsNeedAE⟩
  rw [List.append_assoc]
  exact PairsHost.pairsAE_spec ⟨hsol, by simp, by simp, by simp, by simp, hpre, hok⟩

end ImprovedExponents.AllEdges
