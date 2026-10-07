module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Tile
public import ImprovedExponents.PrunedProgram.Tiles.Contracts

@[expose] public section

/-!
# The trie of one tile, on pruned encodings

Upstream's `tile_spec` proves `tileBody` (procedure 50) under `TilePre`, with the two encodings
of the tile as full arrays, calling `fillList` under `FillListSpec`.  The routine itself reads no
encoding cell; it only hands the encodings on to `fillList`.  So the same body meets the same
specification with the encodings right at the leaves with at most `m` symbols `P₀` only
(`TilePreP`, `tileP_spec`), given `fillList` under `FillListSpecP`.  The proof is upstream's with
`SegOn` in place of `Seg` in the invariant of the loop (`TileP.Mem`); the lemmas `Tile.room`,
`Tile.time_le`, `Tile.trieAt` and `Tile.fillArgs` are reused.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace TileP

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ₁ μ₂ : ℕ → ℤ} {x : TileArgs} {e : ℕ} {σ : State}
  {T T' : List ℤ}

/-- What the memory μ' holds during the loop: the trie array T, the roots, with that of the tile
behind the older ones, and the two encodings at the leaves with few symbols `P₀`; the cells that
the routine does not own are as in μ. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean (Tile.Mem)
structure Mem (μ μ' : ℕ → ℤ) (x : TileArgs) (T : List ℤ) : Prop where
  trie : TrieMem μ' x.tr x.cap x.fp T
  roots : SegN μ' x.aR (x.s.roots ++ [x.s.cells.length])
  segA : SegOn x.m μ' x.aA x.encA
  segB : SegOn x.m μ' x.aB x.encB
  same : SameOn x.Kept μ μ'

/-- After the root of the tile has been taken and written behind the older roots. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean (Tile.Mem.newRoot)
theorem Mem.newRoot (C : TilePreP lim μ x) (hs : SameOutsideTrie μ μ₁ x.tr x.cap x.fp)
    (ht : TrieMem μ₁ x.tr x.cap x.fp T) :
    Mem μ (Function.update μ₁ (x.aR + x.s.roots.length) (x.s.cells.length : ℤ)) x T := by
  have hcells : x.cells = x.s.roots.length + 1 := rfl
  have hlayout := C.ctx.layout
  have hroots := C.rootsPlace
  exact
    { trie := ht.keep
      roots := SegN.snoc C.roots.keep _
      segA := C.segA.keep
      segB := C.segB.keep
      same := by light_keep }

/-- After the boxes with some number of stars have been put into the trie. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean (Tile.Mem.fill)
theorem Mem.fill (C : TilePreP lim μ x) (h : Mem μ μ₁ x T)
    (hs : SameOutsideTile μ₁ μ₂ x.L x.tr x.cap x.fp x.cur x.box)
    (ht : TrieMem μ₂ x.tr x.cap x.fp T') : Mem μ μ₂ x T' := by
  have hcells : x.cells = x.s.roots.length + 1 := rfl
  have hlayout := C.ctx.layout
  have hroots := C.rootsPlace
  have hsame := h.same
  exact { trie := ht, roots := h.roots.keep, segA := h.segA.keep, segB := h.segB.keep
          same := by light_keep }

/-- The state before the boxes with e stars: the root is in its local and in its cell, and the
trie holds the boxes with fewer stars. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean (Tile.Inv)
def Inv (μ : ℕ → ℤ) (x : TileArgs) (e : ℕ) (σ : State) : Prop :=
  ∃ (void : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.aA, x.aB, (x.aR + x.s.roots.length : ℕ), x.tr, x.fp, x.cur, x.box, x.L,
      (x.m - x.t : ℕ), e, x.s.cells.length, void], μ'⟩ ∧
    Mem μ μ' x (Tile.trieAt x e)

/-- One round puts the boxes with e stars into the trie. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean (Tile.round)
theorem round (hFill : FillListSpecP lim P) (C : TilePreP lim μ x) (hd : d + 3 ≤ lim.depth)
    (he : e ≤ x.m - x.t) (h : Inv μ x e σ) :
    Ends lim P d tileRound σ (tFillList x.L (starBoxes x.L x.m x.t e).length + 30)
      (Inv μ x (e + 1)) := by
  obtain ⟨void, μ₁, rfl, hM⟩ := h
  have hlayout := C.ctx.layout
  light_facts C.ctx C.ctx.std
  -- the trie of the tile has the number s.roots.length, and its root is the last one
  have hroot := x.s.root_new
  have hfill := hFill (Tile.fillArgs x e) μ₁
    { ctx := C.ctx, stars_le := he, root_ne := hroot.trans_ne C.rep.length_pos.ne'
      rep := fillUpTo_rep (arrT x.encA) (arrT x.encB) x.m x.t x.s C.rep e
      trie := hM.trie, segA := hM.segA, segB := hM.segB
      room := (Tile.room (arrT x.encA) (arrT x.encB) x.L x.m x.t x.s.cells.length x.s.cells
        he).trans C.room }
  simp only [Tile.fillArgs, FillListArgs.vals, FillListArgs.root, FillListArgs.boxes, hroot]
    at hfill
  -- fillList(e, root, …)
  light_call (hfill _ (by omega)) with void' μ₂ ⟨htrie, same⟩
  -- e := e + 1
  light_set (e + 1 : ℕ)
  exact ⟨void', μ₂, rfl, hM.fill C same htrie⟩

end TileP

open TileP in
/-- **tile on pruned encodings** meets its specification. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean (tile_spec)
theorem tileP_spec {lim : Limits} {P : Program} (hP : P[Proc.tile]? = some tileBody)
    (hNew : NewRootSpec lim P) (hFill : FillListSpecP lim P) : TileSpecP lim P := by
  intro x μ C
  refine fun d hd => ⟨tileBody, hP, ?_⟩
  have hlayout := C.ctx.layout
  light_facts C C.ctx C.ctx.std
  have hcells : x.cells = x.s.roots.length + 1 := rfl
  have hroom := C.room
  unfold tTile
  -- root := newRoot(tr, fp)
  light_call (hNew x.tr x.cap x.fp x.s.cells μ C.trie (by omega) (by omega) (by omega) _
    (by omega)) with _ μ₁ ⟨rfl, htrie, same⟩
  -- mem[ra] := root
  light_store (x.aR + x.s.roots.length) x.s.cells.length
  -- while e ≤ mt
  refine (Ends.while (Inv μ x) (x.m - x.t + 1)
    (fun e => tFillList x.L (starBoxes x.L x.m x.t e).length + 30)
    ?start ?round ?done).mono ?time fun _ h => h
  case start => exact ⟨0, _, congrArg (State.mk · _) (frame_append_zeros _ 1).symm,
    Mem.newRoot C same htrie⟩
  case round =>
    rintro e σ he hI
    have hround := round hFill C hd (by omega) hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    exact ⟨by light_side, by simp; omega, hround⟩
  case done =>
    rintro _ ⟨void, μ', rfl, hM'⟩
    exact ⟨by light_side, by simp, hM'.trie, hM'.roots, hM'.same⟩
  case time =>
    have hsum := Tile.time_le x.L x.m x.t (x.m - x.t + 1)
    -- the test of the loop and the jump cost 6 steps
    have htest : ∀ y : ℕ, 1 + (1 + 1 + 1) + 1 + 1 + y = 6 + y := fun y => by omega
    simp only [Cond.cost, Expr.cost, htest]
    light_time

end Light.Sec4
