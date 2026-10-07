module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts
public import ImprovedExponents.PrunedProgram.SegOn

@[expose] public section

/-!
# The tile preprocessing of Theorem 30 on pruned encodings: specifications

Upstream's routines `fillList`, `tile` and `allTiles` (`ThreeSumApsp/Programs/Sec4/Theorem30/`)
assume the encodings of the two bands of a tile as full arrays, `Seg μ aA (arrT encA)`.  The only
cells they read are those of the leaves with at most `m - t ≤ m` symbols `P₀` (the codes of the
strings of `nineStrs L 0 (m - t)`, in `fillList`).  With the pruned encoder only these cells are
right (`SegOn m μ aA encA`).  This file restates the three assumptions and the three
specifications with `SegOn` in place of `Seg`; the bodies, the procedure numbers, the time
functions, the contexts (`TileCtx`) and all the other fields are upstream's.  The proofs are in
`Tiles/FillList`, `Tiles/Tile` and `Tiles/AllTiles`.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-- What `fillList` assumes on pruned encodings: upstream's `FillListPre`, with the two encodings
right at the leaves with at most `m` symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean (FillListPre)
structure FillListPreP (lim : Limits) (μ : ℕ → ℤ) (x : FillListArgs) : Prop where
  ctx : TileCtx lim x.L x.m x.t x.encA x.encB x.aA x.aB x.tr x.cap x.fp x.cur x.box
  stars_le : x.e ≤ x.m - x.t
  root_ne : x.root ≠ 0
  rep : TrieRep x.L x.lo x.T x.roots (x.stored [])
  trie : TrieMem μ x.tr x.cap x.fp x.T
  segA : SegOn x.m μ x.aA x.encA
  segB : SegOn x.m μ x.aB x.encB
  room : x.T.length + 11 * x.L * x.boxes.length ≤ x.cap

/-- fillList(e, root, aA, aB, tr, fp, cur, box, L, mt) on pruned encodings: upstream's
`FillListSpec` with `FillListPreP`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean (FillListSpec)
def FillListSpecP (lim : Limits) (P : Program) : Prop :=
  ∀ (x : FillListArgs) (μ : ℕ → ℤ), FillListPreP lim μ x →
    ∀ d, d + 2 ≤ lim.depth →
    Meets lim P Proc.fillList d x.vals μ (tFillList x.L x.boxes.length) fun _ μ' =>
      TrieMem μ' x.tr x.cap x.fp (fillTrie (arrT x.encA) (arrT x.encB) x.root x.e x.boxes x.T) ∧
        SameOutsideTile μ μ' x.L x.tr x.cap x.fp x.cur x.box

/-- What `tile` assumes on pruned encodings: upstream's `TilePre`, with the two encodings right at
the leaves with at most `m` symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean (TilePre)
structure TilePreP (lim : Limits) (μ : ℕ → ℤ) (x : TileArgs) : Prop where
  ctx : TileCtx lim x.L x.m x.t x.encA x.encB x.aA x.aB x.tr x.cap x.fp x.cur x.box
  rep : x.s.Holds x.L x.lo x.old
  trie : TrieMem μ x.tr x.cap x.fp x.s.cells
  roots : SegN μ x.aR x.s.roots
  segA : SegOn x.m μ x.aA x.encA
  segB : SegOn x.m μ x.aB x.encB
  room : x.s.cells.length + 11 * (1 + x.L * (boxes x.L x.m x.t).card) ≤ x.cap
  /-- The cells of the roots lie between the cell fp and the trie area. -/
  rootsPlace : x.fp < x.aR ∧ x.aR + x.cells ≤ x.tr

/-- `tile` on pruned encodings: upstream's `TileSpec` with `TilePreP`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean (TileSpec)
def TileSpecP (lim : Limits) (P : Program) : Prop :=
  ∀ (x : TileArgs) (μ : ℕ → ℤ), TilePreP lim μ x →
    ∀ d, d + 3 ≤ lim.depth → Meets lim P Proc.tile d
      [x.aA, x.aB, (x.aR + x.s.roots.length : ℕ), x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ)] μ
      (tTile x.L x.m x.t) fun _ μ' =>
        TrieMem μ' x.tr x.cap x.fp x.tries.cells ∧ SegN μ' x.aR x.tries.roots ∧ SameOn x.Kept μ μ'

/-- What `allTiles` assumes on pruned encodings: upstream's `AllTilesPre`, with the encoding of
every band right at the leaves with at most `m` symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean (AllTilesPre)
structure AllTilesPreP (lim : Limits) (μ : ℕ → ℤ) (x : AllTilesArgs) : Prop where
  std : Std lim
  t_le : x.t ≤ x.m
  m_le : x.m ≤ x.L
  /-- Every value and every partial sum fits in a word. -/
  value_le : ∃ A B : ℤ, (∀ β τ, |x.encA β τ| ≤ A) ∧ (∀ β τ, |x.encB β τ| ≤ B) ∧
    10 ^ x.m * (A * B) ≤ lim.word
  pow_le : (10 : ℤ) ^ x.L ≤ lim.word
  cap_ge : 1 + x.nB * x.nB * (11 * (1 + x.L * (boxes x.L x.m x.t).card)) ≤ x.cap
  /-- The areas lie in this order, without overlap, below the end of the memory. -/
  order : x.aENCA + x.nB * 10 ^ x.L ≤ x.aENCB ∧ x.aENCB + x.nB * 10 ^ x.L ≤ x.cur ∧
    x.cur + x.L ≤ x.box ∧ x.box + x.L ≤ x.fp ∧ x.fp < x.aR ∧
    x.aR + x.nB * x.nB ≤ x.tr ∧ x.tr + x.cap < lim.space
  segA : ∀ β < x.nB, SegOn x.m μ (x.aENCA + β * 10 ^ x.L) (x.encA β)
  segB : ∀ β < x.nB, SegOn x.m μ (x.aENCB + β * 10 ^ x.L) (x.encB β)
  trie : TrieMem μ x.tr x.cap x.fp [0]

/-- `allTiles` on pruned encodings: upstream's `AllTilesSpec` with `AllTilesPreP`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean (AllTilesSpec)
def AllTilesSpecP (lim : Limits) (P : Program) : Prop :=
  ∀ (x : AllTilesArgs) (μ : ℕ → ℤ), AllTilesPreP lim μ x →
    ∀ d, d + 4 ≤ lim.depth →
    Meets lim P Proc.allTiles d [x.aENCA, x.aENCB, x.nB, (10 ^ x.L : ℕ), x.aR, x.tr, x.fp,
      x.cur, x.box, x.L, (x.m - x.t : ℕ)] μ (tAllTiles x.L x.m x.t x.nB) fun _ μ' =>
        TrieMem μ' x.tr x.cap x.fp x.tries.cells ∧ SegN μ' x.aR x.tries.roots ∧ SameOn x.Kept μ μ'

end Light.Sec4
