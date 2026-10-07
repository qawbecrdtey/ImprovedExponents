module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Program
public import ImprovedExponents.PrunedProgram.Pre.Defs
public import ImprovedExponents.PrunedProgram.Tiles.FillList
public import ImprovedExponents.PrunedProgram.Tiles.Tile
public import ImprovedExponents.PrunedProgram.Tiles.AllTiles

@[expose] public section

/-!
# The preprocessing of Theorem 30 with the pruned shared stage

Upstream's `preCoreBody` runs the shared stage `Sec2.pShared`, notes `t` in the directory,
computes the addresses of the areas of Section 4 (`preCoreAddr`) and builds the tries of all
tiles (`preCoreFinish`).  The new procedure `preCoreP` (`preCorePBody`) is the same statement
with the pruned shared stage `Proc.sharedP` in place of `Sec2.pShared`: it leaves the encodings
right at the leaves with at most `m` symbols `P₀` only (`Sec2.SharedReadyP`), which is all that
`allTiles` on pruned encodings assumes (`AllTilesPreP`), and it establishes `DSReadyP` in the
time `tPreCoreP`.  The proofs are upstream's with `SharedReadyP` in place of `SharedReady`:

* `SharedReadyP.dirCells`: the cells of the directory that the routine reads.
* `preCoreAddrP_spec`, `allArgsP_pre`, `preCoreFinishP_spec`, `preCoreP_spec`: the parts of
  the routine and the routine (`preCore_spec`), under `Sec2.SharedSpecP` and `AllTilesSpecP`.
* `preCoreP_of_base58`: for a program `base58 ++ R` that holds `preCorePBody` at `Proc.preCoreP`
  and meets `Sec2.SharedSpecP`, the specification `PreCoreSpecP` holds; the bodies and the
  specifications of upstream's routines 40 to 48 come from `at_base58` and `specs40`.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Directory.lean`, `Areas.lean`,
`Preprocessing.lean`, `Routines.lean` and `Program.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The program -/

open PreCore in
/-- preCoreP(L, m, t, N, D, aX, aY, b0) builds the data structure for the matrices at aX and aY in
the block from b0 on, with the pruned shared stage: upstream's `preCoreBody` with `Proc.sharedP`
in place of `Sec2.pShared`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean (preCoreBody)
def preCorePBody : Stmt :=
  .call Proc.sharedP [v Levels, v Inner, v Size, v Width, v MatX, v MatY, v Base] Void ;;
  .store (v Base +' k Dir.switch) (v Switch) ;;
  preCoreAddr ;;
  preCoreFinish

/-! ## The addresses -/

/-- The addresses of the areas of Section 4 are computed as the map says. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean
-- (preCoreAddr_spec)
theorem preCoreAddrP_spec (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U)
    (hSR : Sec2.SharedReadyP p hmL aX aY b0 X Y μ) (r : ℤ) :
    Ends lim P d preCoreAddr ⟨frame (preShared p t aX aY b0 r), μ⟩ 38
      (· = ⟨frame (preLocals p t aX aY b0 r), μ⟩) := by
  have dir := hSR.dirCells
  light_facts hlim hlim.std
  obtain ⟨⟩ := areas p t b0
  unfold preLocals preShared
  -- the product nB², in the integers
  have hsq : ((p.nB * p.nB : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.nB * p.nB ≤ lim.space)
  have htr : ((aROOTS p b0 + p.nB * p.nB : ℕ) : ℤ) = aTR p b0 := by
    exact_mod_cast (by omega : aROOTS p b0 + p.nB * p.nB = aTR p b0)
  have hsq0 : (0 : ℤ) ≤ (p.nB : ℤ) * p.nB := by positivity
  push_cast at hsq htr
  -- digits := dir[30]; bands := dir[9]
  light_set (aWD p b0 : ℕ) using dir.sharedEnd
  light_set (p.nB : ℕ) using dir.bands
  -- cur := digits + L; box := cur + L; free := box + L + m; roots := free + 1
  light_set (aCUR p b0 : ℕ)
  light_set (aBOX p b0 : ℕ)
  light_set (aFP p b0 : ℕ)
  light_set (aROOTS p b0 : ℕ)
  -- last := m - t; tries := roots + nB nB
  light_set (p.m - t : ℕ)
  light_set (aTR p b0 : ℕ)
  rfl

/-! ## The tries -/

/-- The block, after the pruned shared stage and with the trie array [0], holds what allTiles on
pruned encodings assumes. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean (allArgs_pre)
theorem allArgsP_pre (h : Lim30 lim p t b0 U) (ht : t ≤ p.m) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hSR : Sec2.SharedReadyP p hmL aX aY b0 X Y μ)
    (hTM : TrieMem μ (aTR p b0) (trieCap p t) (aFP p b0) [0]) :
    AllTilesPreP lim μ (allArgs p t hmL b0 X Y) := by
  -- a negative bound U is possible only if there are no entries; then 0 is a bound as well
  obtain ⟨U', hU0, hX', hY', hvalue⟩ : ∃ U' : ℤ, 0 ≤ U' ∧ (∀ i j, |X i j| ≤ U') ∧
      (∀ i j, |Y i j| ≤ U') ∧ 10 ^ p.m * ((7 ^ p.L * U') * (7 ^ p.L * U')) ≤ lim.word := by
    rcases le_or_gt 0 U with h0 | h0
    · exact ⟨U, h0, hX, hY, h.value⟩
    · have hword : (0 : ℤ) ≤ lim.word := le_trans (by norm_num) h.std.const_le
      exact ⟨0, le_rfl, fun i j => absurd ((abs_nonneg _).trans (hX i j)) (not_le.mpr h0),
        fun i j => absurd ((abs_nonneg _).trans (hY i j)) (not_le.mpr h0), by simpa using hword⟩
  have hsp := h.space
  have hT : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  exact
    { std := h.std
      t_le := ht
      m_le := hmL
      value_le := ⟨7 ^ p.L * U', 7 ^ p.L * U',
        fun β τ => (abs_enc_le hmL X Y U' hU0 hX' hY' β β).1 τ,
        fun β τ => (abs_enc_le hmL X Y U' hU0 hX' hY' β β).2 τ, hvalue⟩
      pow_le := h.pow_le
      cap_ge := le_rfl
      order := by simp only [allArgs]; rw [hT]; omega
      segA := fun β hβ => hSR.encA β hβ
      segB := fun β hβ => hSR.encB β hβ
      trie := hTM }

/-- After the pruned shared stage, the last part completes the data structure; it changes only
cells from CUR to the end of the block. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean
-- (preCoreFinish_spec)
theorem preCoreFinishP_spec (hAll : AllTilesSpecP lim P) (hlim : Lim30 lim p t b0 U)
    (ht : t ≤ p.m) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (hd : d + 5 ≤ lim.depth)
    (r : ℤ) (hSR : Sec2.SharedReadyP p hmL aX aY b0 X Y μ) (hcellT : μ (b0 + 31) = t) :
    Ends lim P d preCoreFinish ⟨frame (preLocals p t aX aY b0 r), μ⟩
      (tAllTiles p.L p.m t p.nB + 28) fun σ' =>
      DSReadyP p t hmL aX aY b0 X Y σ'.mem ∧
        SameOutside μ σ'.mem (aCUR p b0) (top p t b0 - aCUR p b0) := by
  light_facts hlim hlim.std
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold preLocals preShared
  -- TR[0] := 0; FP := 1
  light_store (aTR p b0) 0
  light_store (aFP p b0) 1
  have hTM := trieMem_start p t b0 μ
  have same : SameOutside μ (Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1)
      (aCUR p b0) (top p t b0 - aCUR p b0) :=
    (SameOutside.refl.update (by omega) 0).update (by omega) 1
  generalize Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1 = μ₁ at *
  have hSR₁ : Sec2.SharedReadyP p hmL aX aY b0 X Y μ₁ :=
    hSR.of_agree fun b hb _ => same b (Or.inl (by omega))
  have dir := hSR₁.dirCells
  -- the tries of all tiles
  light_call (hAll _ μ₁ (allArgsP_pre hlim ht hX hY hSR₁ hTM))
    using allArgs, dir.encA, dir.encB, dir.leaves, Sec2.Par.T with r' μ₂ ⟨hTM₂, hroots, same₂⟩
  have same' : SameOutside μ μ₂ (aCUR p b0) (top p t b0 - aCUR p b0) :=
    same.then same₂ fun b hb =>
      ⟨hb, by change b < aCUR p b0 ∨ aTR p b0 + trieCap p t ≤ b; omega⟩
  exact ⟨⟨hSR.of_agree fun b hb _ => same' b (Or.inl (by omega)),
    (same' _ (Or.inl (by omega))).trans hcellT, hroots, hTM₂.seg⟩, same'⟩

/-! ## The routine -/

/-- **preCoreP** meets its specification: the pruned shared stage, then upstream's own parts. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean (preCore_spec)
theorem preCoreP_spec {c : ℕ} (hP : P[Proc.preCoreP]? = some preCorePBody)
    (hShared : Sec2.SharedSpecP lim P c) (hAll : AllTilesSpecP lim P) :
    PreCoreSpecP lim P c := by
  intro p t hmL aX aY b0 X Y U μ ht hlim hX hY hMX hMY haX haY
  refine fun d hd => ⟨preCorePBody, hP, ?_⟩
  light_facts hlim hlim.std
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold tPreCoreP
  -- the pruned shared stage
  light_call (hShared p hmL aX aY b0 μ X Y U
    { space := by omega, matX := hMX, matY := hMY, belowX := haX, belowY := haY, absX := hX
      absY := hY, seven := hlim.enc, ten := hlim.pow }) with r μ₁ ⟨hSR₁, same₁⟩
  -- dir[31] := t
  light_store (b0 + 31) t
  have hSR₂ : Sec2.SharedReadyP p hmL aX aY b0 X Y (Function.update μ₁ (b0 + 31) t) :=
    hSR₁.of_agree fun b _ hb => Function.update_of_ne hb ..
  -- the addresses
  light_piece (preCoreAddrP_spec ht hlim hSR₂ r) with _ rfl
  -- the tries
  refine (preCoreFinishP_spec hAll hlim ht hX hY (by omega) r hSR₂
    (Function.update_self ..)).mono (by simp; omega) ?_
  rintro σ' ⟨hDS, same₂⟩
  refine ⟨hDS, fun b hb => ?_⟩
  rw [same₂ b (by omega), Function.update_of_ne (by omega), same₁ b (by omega)]

/-! ## In a program that begins with `base58` -/

/-- **The preprocessing with the pruned shared stage**, in every program that begins with
upstream's `base58`, holds `preCorePBody` at `Proc.preCoreP` and meets the specification of the
pruned shared stage.  The routines 40 to 48 are upstream's (`specs40`), and so are the bodies of
`fillList`, `tile` and `allTiles`, which are re-verified on pruned encodings. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Routines.lean (preCoreSpec_of,
-- preCoreSpec_all) and Program.lean (preCore_base58)
theorem preCoreP_of_base58 {P R : Program} {c : ℕ} (hP : P = base58 ++ R)
    (hpre : P[Proc.preCoreP]? = some preCorePBody) (hsh : Sec2.SharedSpecP lim P c) :
    PreCoreSpecP lim P c := by
  intro p t hmL aX aY b0 X Y U μ ht hlim
  have h40 : Has40 P := hP ▸ has40_base58 R
  have S := specs40 h40 hlim.std
  have hFill : FillListSpecP lim P :=
    fillListP_meets (h40 9 (by omega)) S.nineFirst S.nineNext S.starFirst S.horner S.insert
      S.sumTen
  have hTile : TileSpecP lim P := tileP_spec (h40 10 (by omega)) S.newRoot hFill
  have hAll : AllTilesSpecP lim P := allTilesP_spec (h40 11 (by omega)) hTile
  exact preCoreP_spec hpre hsh hAll p t hmL aX aY b0 X Y U μ ht hlim

end Light.Sec4
