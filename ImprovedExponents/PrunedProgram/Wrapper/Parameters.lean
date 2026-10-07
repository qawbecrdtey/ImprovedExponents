module

public import ImprovedExponents.PrunedProgram.Wrapper.Times

@[expose] public section

/-!
# Corollary 31 with the pruned encoder: the state of the routines and the query

Upstream's routines with rational parameters (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/
Parameters.lean`) keep, from the free pointer on, a flag, the base address and the data structure
of Theorem 30 for the padded matrices (`Built31`, `Ready31`).  With the pruned encoder the data
structure is `DSReadyP` (the encodings right at the leaves with at most `m` symbols `P₀`):
`Built31P`, `Ready31P`.  The query `query31` is upstream's own procedure and body; it meets the
same specification with `Ready31P` (`query31P_meets`) from `QueryAtSpecP`.  The preprocessing
`pre31P` is upstream's `pre31` with `preCoreP` in place of `preCore` (`pre31PBody`, `PreSpec31P`).

Adapted from upstream (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-- The data structure of Theorem 30 with pruned encodings for the padded matrices has been built
in the cells after fr. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (Built31)
abbrev Built31P (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (fr : ℕ) (μ : ℕ → ℤ) : Prop :=
  DSReadyP (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
    (paddedYAt N D₀ fr) (blockAt N D₀ fr) (padInnerCols (D (logFour D₀)) X)
    (padInnerRows (D (logFour D₀)) Y) μ

/-- **The cells from fr on hold what a query needs**, with pruned encodings. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (Ready31)
structure Ready31P (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (μ : ℕ → ℤ) : Prop where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  small : logFour D₀ < G.m₀ → μ fr = 0
  large : G.m₀ ≤ logFour D₀ → μ fr = 1 ∧ μ (fr + 1) = blockAt N D₀ fr ∧ Built31P G X Y fr μ

/-- query31 returns the entry (XY)[I, J], keeps the structure ready, and changes only cells of the
structure behind its first three: upstream's procedure, with pruned encodings. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (QuerySpec31)
def QuerySpec31P (lim : Limits) (P : Program) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ) (I J : Fin N), Input31 lim G X Y aX aY fr U → Ready31P G X Y aX aY fr μ →
    ∀ d, d + 3 ≤ lim.depth → Meets lim P Proc.query31 d [(I : ℕ), (J : ℕ), N, D₀, aX, aY, fr] μ
        (tQuery31 G D₀) fun r μ' =>
      r = (X * Y) I J ∧ Ready31P G X Y aX aY fr μ' ∧
          SameOutside μ μ' (fr + 3) (structEnd G N D₀ fr - (fr + 3))

/-- A query to the data structure of Theorem 30 changes only cells of its block, so that the
structure stays ready. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean
-- (Ready31.of_query)
theorem Ready31P.of_query (h : Ready31P G X Y aX aY fr μ) (bX : aX + N * D₀ ≤ fr)
    (bY : aY + D₀ * N ≤ fr) (hm : G.m₀ ≤ logFour D₀) (hkept : ∀ a < blockAt N D₀ fr, μ' a = μ a)
    (hDS : Built31P G X Y fr μ') : Ready31P G X Y aX aY fr μ' := by
  have hb0 := add_three_le_blockAt N D₀ fr
  obtain ⟨hflag, hbase, -⟩ := h.large hm
  exact ⟨h.matX.congr_below hkept (by omega), h.matY.congr_below hkept (by omega),
    fun hm' => absurd hm (by omega),
    fun _ => ⟨(hkept _ (by omega)).trans hflag, (hkept _ (by omega)).trans hbase, hDS⟩⟩

/-- query31 reads the flag and calls the query of Theorem 30 if it is 1 and the inner product
otherwise; it returns the entry (XY)[I, J] and keeps the structure ready. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean
-- (query31_meets)
theorem query31P_meets (G : RatParams) (hP : P[Proc.query31]? = some query31Body)
    (hq : QueryAtSpecP lim P) (hip : IpAtSpec lim P) : QuerySpec31P lim P G := by
  intro N D₀ aX aY fr X Y U μ I J hin hR
  have hlim := hin.lim
  have bX := hin.belowX
  have bY := hin.belowY
  refine fun d hd => ⟨query31Body, hP, ?_⟩
  have hw := hlim.std.space_le
  have h100 := hlim.std.const_le
  have hU0 := hin.zero_le_U
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hsp := hlim.space
  unfold query31Body
  -- if mem[fr] = 1
  refine Ends.iteLast (fun hflag => ?_) (fun hflag => ?_) (hT := by simp [tQuery31])
  · -- the data structure has been built: return queryAt(I, J, mem[fr + 1])
    have hlarge : G.m₀ ≤ logFour D₀ := by
      by_contra hc
      have hzero := hR.small (by omega)
      have hone : μ fr = 1 := by simpa using hflag
      omega
    obtain ⟨-, hbase, hDS⟩ := hR.large hlarge
    have haddr : ((fr : ℤ) + 1).toNat = fr + 1 := by omega
    refine Ends.callTo
      (hq (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
        (paddedYAt N D₀ fr) (blockAt N D₀ fr) _ _ U μ I J (G.t_le _) (hlim.large hlarge)
        (abs_padInnerCols_le hin.absX hU0) (abs_padInnerRows_le hin.absY hU0) hDS _ (by omega)) ?_
      (by light_side [haddr, hbase])
      (hT := by simp [tQuery31, ite_eq_right (not_lt.mpr hlarge), parOf]; omega)
    rintro r μ' ⟨hr, hDS', hout⟩
    have hscratch := G.scratch_in_block N D₀ fr
    have hb0 := add_three_le_blockAt N D₀ fr
    have htop := structEnd_large hlarge N fr
    refine ⟨?_, hR.of_query bX bY hlarge (fun a ha => hout a (by omega)) hDS',
      fun a ha => hout a (by omega)⟩
    -- padding changes no entry of the product
    exact hr.trans (congrFun (congrFun
      (Corollary26.padding (D (logFour D₀)) (le_D_logFour D₀) X Y) I) J)
  · -- m is below the threshold: return the inner product ipAt(I, J, N, D, aX, aY)
    have hsmall : logFour D₀ < G.m₀ := by
      by_contra hc
      exact hflag (by simpa using (hR.large (by omega)).1)
    refine Ends.callTo (hip N D₀ aX aY X Y U μ I J hin.one_le_D hR.matX hR.matY hin.absX hin.absY
      (by omega) (by omega) hlim.ip _ (by omega)) ?_
      (hT := by simp [tQuery31, ite_eq_left hsmall]; omega)
    rintro r μ' ⟨hr, rfl⟩
    exact ⟨hr, hR, .refl⟩

/-! ## The preprocessing: text and interface -/

open Pre31 in
/-- The second part of pre31P: the preprocessing of Theorem 30 with the pruned encoder, the base
address and the flag 1. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (preBuild31)
def preBuild31P : Stmt :=
  .call Proc.preCoreP [v Levels, v Log, v Switch, v Size, v Padded, v PadX, v PadY, v Block] Res ;;
  .store (v Free +' k 1) (v Block) ;;
  .store (v Free) (k 1)

/-- The part of pre31P for m ≥ m₀. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (preLarge31)
def preLarge31P : Stmt := prePad31 ;; preBuild31P

open Pre31 in
/-- pre31P(N, D, aX, aY, fr): m and 4^m; for m < m₀ the flag 0, for m ≥ m₀ preLarge31P. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (pre31Body)
def pre31PBody (G : RatParams) : Stmt :=
  .call Proc.log4 [v Dim, v Free +' k 2] Log ;;
  .ite (v Log <' k G.m₀) (.store (v Free) (k 0)) preLarge31P

/-- pre31P prepares the cells from fr on, about which nothing is assumed, for queries to XY. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (PreSpec31)
def PreSpec31P (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ), Input31 lim G X Y aX aY fr U → MatAt μ aX X → MatAt μ aY Y →
    ∀ d, d + (G.L (logFour D₀) + 7) ≤ lim.depth → Meets lim P Proc.pre31P d [N, D₀, aX, aY, fr] μ
        (tPre31P c G N D₀) fun _ μ' =>
      Ready31P G X Y aX aY fr μ' ∧ SameOutside μ μ' fr (structEnd G N D₀ fr - fr)

end Light.Sec4
