module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.AllTiles
public import ImprovedExponents.PrunedProgram.Tiles.Contracts
import all ThreeSumApsp.Programs.Sec4.Theorem30.AllTiles

@[expose] public section

/-!
# The tries of all tiles, on pruned encodings

Upstream's `allTiles_spec` proves `allTilesBody` (procedure 51) under `AllTilesPre`, with the
encodings of all bands as full arrays, calling `tile` under `TileSpec`.  The routine reads no
encoding cell; it only computes the addresses of the two encodings of each tile and hands them
on.  So the same body meets the same specification with the encodings right at the leaves with
at most `m` symbols `P₀` only (`AllTilesPreP`, `allTilesP_spec`), given `tile` under `TileSpecP`.
The proof is upstream's; only `tileArgs_pre` changes, which carries the encodings of the two
bands (`SegOn.keep` in place of `Seg.keep`).  The invariant `AllTiles.Mem` and the lemmas
`AllTiles.triesBefore`, `AllTiles.tileArgs` are reused.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

open private length_roots_triesBefore tries_tileArgs time_le
  from ThreeSumApsp.Programs.Sec4.Theorem30.AllTiles

namespace AllTilesP

open AllTiles

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : AllTilesArgs} {β β' : ℕ} {σ : State}

/-- The surroundings of the tile (β, β'). -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (AllTiles.tileCtx)
private theorem tileCtx (C : AllTilesPreP lim μ x) (hβ : β < x.nB) (hβ' : β' < x.nB) :
    TileCtx lim x.L x.m x.t (x.encA β) (x.encB β') (x.aENCA + β * 10 ^ x.L)
      (x.aENCB + β' * 10 ^ x.L) x.tr x.cap x.fp x.cur x.box := by
  have horder := C.order
  have hrow := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
  have hcol := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  obtain ⟨A, B, hA, hB, hAB⟩ := C.value_le
  generalize β * 10 ^ x.L = a at *
  generalize β' * 10 ^ x.L = b at *
  generalize x.nB * 10 ^ x.L = z at *
  generalize x.nB * x.nB = q at *
  exact
    { std := C.std, ht := C.t_le, hmL := C.m_le, value_le := ⟨A, B, hA β, hB β', hAB⟩
      pow_le := C.pow_le, layout := by light_order }

/-- Before the tile (β, β') the memory holds what tile assumes: the encodings of the two bands
are right at the leaves with few symbols `P₀`, as nothing below cur has changed. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean
-- (AllTiles.tileArgs_pre)
private theorem tileArgs_pre (C : AllTilesPreP lim μ x) (hβ : β < x.nB) (hβ' : β' < x.nB)
    {μ' : ℕ → ℤ} (M : Mem μ μ' x β β') : TilePreP lim μ' (tileArgs x β β') := by
  light_facts C
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hrow := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
  have hcol := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  have hlenR := length_roots_triesBefore x β β'
  have hlenT := length_allTries_le x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')
  rw [length_tilesBefore] at hlenT
  have hroom := Nat.mul_add_le_mul hi (le_refl (11 * (1 + x.L * (boxes x.L x.m x.t).card)))
  have hA : SegOn x.m μ' (x.aENCA + β * 10 ^ x.L) (x.encA β) :=
    (C.segA β hβ).keep (by light_keep [M.same])
  have hB : SegOn x.m μ' (x.aENCB + β' * 10 ^ x.L) (x.encB β') :=
    (C.segB β' hβ').keep (by light_keep [M.same])
  have hlenT' : (triesBefore x β β').cells.length
      ≤ 1 + (β * x.nB + β') * (11 * (1 + x.L * (boxes x.L x.m x.t).card)) := hlenT
  exact
    { ctx := tileCtx C hβ hβ'
      rep := allTries_rep x.L x.m x.t _
      trie := M.trie
      roots := M.roots
      segA := hA
      segB := hB
      room := by simp only [tileArgs]; omega
      rootsPlace := by simp only [tileArgs, TileArgs.cells]; omega }

/-- The call of `tile` for the tile (β, β') leads from the memory before this tile to the memory
before the next one. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (AllTiles.tile_meets)
private theorem tile_meets (hTile : TileSpecP lim P) (C : AllTilesPreP lim μ x) (hβ : β < x.nB)
    (hβ' : β' < x.nB) (hd : d + 3 ≤ lim.depth) {μ' : ℕ → ℤ} (M : Mem μ μ' x β β') :
    Meets lim P Proc.tile d [(x.aENCA + β * 10 ^ x.L : ℕ), (x.aENCB + β' * 10 ^ x.L : ℕ),
      (x.aR + (β * x.nB + β') : ℕ), x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ)] μ'
      (tTile x.L x.m x.t) fun _ μ'' => Mem μ μ'' x β (β' + 1) := by
  have horder := C.order
  have hlenR := length_roots_triesBefore x β β'
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hmeets := hTile _ μ' (tileArgs_pre C hβ hβ' M) _ hd
  rw [← hlenR]
  refine hmeets.mono le_rfl fun _ μ'' ⟨htrie, hroots, same⟩ =>
    ⟨tries_tileArgs x β β' ▸ htrie, tries_tileArgs x β β' ▸ hroots,
      M.same.then same fun c hc => ⟨hc, ?_⟩⟩
  -- a cell below cur or behind the trie area is none of those that tile may change
  have hc' : c < x.cur ∨ x.tr + x.cap ≤ c := hc
  simp only [TileArgs.Kept, tileArgs, Outside]
  omega

/-- One tile: the call, and the pointers move on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (AllTiles.step_spec)
private theorem step_spec (hTile : TileSpecP lim P) (C : AllTilesPreP lim μ x) (hβ : β < x.nB)
    (hβ' : β' < x.nB) (hd : d + 4 ≤ lim.depth) (h : Inv μ x β β' σ) :
    Ends lim P d allTilesStep σ (tTile x.L x.m x.t + 23) (Inv μ x β (β' + 1)) := by
  obtain ⟨void, μ₁, rfl, M⟩ := h
  light_facts C C.std
  -- tile(rowEnc, colEnc, rootPtr, …)
  light_call (tile_meets hTile C hβ hβ' (by omega) M) with void' μ₂ M₂
  -- rootPtr := rootPtr + 1; colEnc := colEnc + leaves; colBand := colBand + 1
  have hptr : x.aR + (β * x.nB + (β' + 1)) = x.aR + (β * x.nB + β') + 1 := by ring
  have hcol : x.aENCB + (β' + 1) * 10 ^ x.L = x.aENCB + β' * 10 ^ x.L + 10 ^ x.L := by ring
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hcolS := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  have hbands : x.nB ≤ x.nB * 10 ^ x.L := Nat.le_mul_of_pos_right _ (by positivity)
  unfold AllTiles.Inv
  rw [hptr, hcol]
  -- names for the products
  generalize β * x.nB + β' = ptr at *
  generalize x.aENCA + β * 10 ^ x.L = row at *
  generalize β' * 10 ^ x.L = off at *
  generalize x.nB * 10 ^ x.L = all at *
  generalize 10 ^ x.L = leaves at *
  light_set (x.aR + ptr + 1 : ℕ)
  light_set (x.aENCB + off + leaves : ℕ)
  light_set (β' + 1 : ℕ)
  exact ⟨void', μ₂, rfl, M₂⟩

/-- One row of tiles. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (AllTiles.row_spec)
private theorem row_spec (hTile : TileSpecP lim P) (C : AllTilesPreP lim μ x) (hβ : β < x.nB)
    (hd : d + 4 ≤ lim.depth) (h : Inv μ x β 0 σ) :
    Ends lim P d allTilesRow σ (x.nB * (tTile x.L x.m x.t + 27) + 16) (Inv μ x (β + 1) 0) := by
  light_facts C C.std
  -- while β' < nB: one tile
  refine Ends.next _ (Ends.whileConst (Inv μ x β) x.nB (tTile x.L x.m x.t + 23) h ?round ?done
    le_rfl) (by simp; ring_nf; omega)
  case round =>
    rintro β' σ hβ' hI
    have hstep := step_spec hTile C hβ hβ' hd hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    exact ⟨by simp, by simpa using hβ', hstep⟩
  case done =>
    rintro _ ⟨void, μ', rfl, M⟩
    refine ⟨by simp, by simp, ?_⟩
    -- rowEnc := rowEnc + leaves; rowBand := rowBand + 1; colBand := 0; colEnc := encB
    have hptr : x.aR + ((β + 1) * x.nB + 0) = x.aR + (β * x.nB + x.nB) := by ring
    have hrow : x.aENCA + (β + 1) * 10 ^ x.L = x.aENCA + β * 10 ^ x.L + 10 ^ x.L := by ring
    have hcol : x.aENCB + 0 * 10 ^ x.L = x.aENCB := by ring
    have hrowS := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
    have hbands : x.nB ≤ x.nB * 10 ^ x.L := Nat.le_mul_of_pos_right _ (by positivity)
    have hbefore : triesBefore x β x.nB = triesBefore x (β + 1) 0 := by
      rw [triesBefore, tilesBefore_row, triesBefore]
    have M' : Mem μ μ' x (β + 1) 0 := ⟨hbefore ▸ M.trie, hbefore ▸ M.roots, M.same⟩
    unfold AllTiles.Inv
    rw [hptr, hrow, hcol]
    -- names for the products
    generalize x.aR + (β * x.nB + x.nB) = ptr at *
    generalize β * 10 ^ x.L = off at *
    generalize x.nB * 10 ^ x.L = all at *
    generalize 10 ^ x.L = leaves at *
    light_set (x.aENCA + off + leaves : ℕ)
    light_set (β + 1 : ℕ)
    light_set (0 : ℕ)
    light_set (x.aENCB : ℕ)
    exact ⟨void, μ', rfl, M'⟩

end AllTilesP

open AllTiles AllTilesP in
/-- **allTiles on pruned encodings** meets its specification. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (allTiles_spec)
theorem allTilesP_spec {lim : Limits} {P : Program} (hP : P[Proc.allTiles]? = some allTilesBody)
    (hTile : TileSpecP lim P) : AllTilesSpecP lim P := by
  intro x μ C
  refine fun d hd => ⟨allTilesBody, hP, ?_⟩
  light_facts C.std
  have htime := time_le x.nB (tTile x.L x.m x.t)
  unfold tAllTiles
  -- β := 0; β' := 0; the three pointers at the first tile
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (x.aR : ℕ)
  light_set (x.aENCA : ℕ)
  light_set (x.aENCB : ℕ)
  light_set 0
  -- while β < nB: one row
  refine Ends.whileConst (fun β => Inv μ x β 0) x.nB (x.nB * (tTile x.L x.m x.t + 27) + 16) ?start
    ?round ?done (by simp; omega)
  case start =>
    refine ⟨0, μ, by simp, ?_, ?_, .refl⟩
    · rw [triesBefore, tilesBefore_zero]
      exact C.trie
    · rw [triesBefore, tilesBefore_zero]
      simp [allTries, SegN, Seg]
  case round =>
    rintro β σ hβ hI
    have hrow := row_spec hTile C hβ hd hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    exact ⟨by simp, by simpa using hβ, hrow⟩
  case done =>
    rintro _ ⟨void, μ', rfl, M⟩
    have hall : triesBefore x x.nB 0 = x.tries := by
      rw [triesBefore, tilesBefore_all, AllTilesArgs.tries]
    exact ⟨by simp, by simp, hall ▸ M.trie, hall ▸ M.roots, M.same⟩

end Light.Sec4
