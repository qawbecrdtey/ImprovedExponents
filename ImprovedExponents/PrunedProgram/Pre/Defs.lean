module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Directory
public import ImprovedExponents.PrunedProgram.Shared.Contracts

@[expose] public section

/-!
# The data structure of Theorem 30 built on pruned encodings: invariant, time and specifications

Upstream's `DSReady` says that the block from `b0` on holds the data structure for `X` and `Y`:
the shared stage's tables, directory and encodings (`SharedReady`), the switch `t`, the roots and
the tries.  With the pruned encoder the encodings are right at the leaves with at most `m`
symbols `P₀` only (`SharedReadyP`), which is all the tile preprocessing and the queries read.
`DSReadyP` is `DSReady` with `SharedReadyP` in place of `SharedReady`; `PreCoreSpecP` and
`QueryAtSpecP` are the specifications of the preprocessing (new procedure `preCoreP`) and of
upstream's own query routine `queryAt` with this invariant; `tPreCoreP` is `tPreCore` with the
shape `sharedShapeP` of the pruned shared stage.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Memory.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents

/-- **The block from b0 on holds the data structure for X and Y**, with the encodings right at the
leaves with at most `m` symbols `P₀`.  The pruned preprocessing establishes this, and every query
needs it and keeps it. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Memory.lean (DSReady)
structure DSReadyP (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (μ : ℕ → ℤ) : Prop where
  shared : Sec2.SharedReadyP p hmL aX aY b0 X Y μ
  cellT : μ (b0 + 31) = t
  roots : SegN μ (aROOTS p b0) (dsTries p t hmL X Y).roots
  trie : Seg μ (aTR p b0) (dsTries p t hmL X Y).cells

section

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- The full data structure is in particular one with the encodings right at the leaves with few
symbols `P₀`. -/
theorem DSReady.toP (h : DSReady p t hmL aX aY b0 X Y μ) : DSReadyP p t hmL aX aY b0 X Y μ :=
  ⟨h.shared.toP, h.cellT, h.roots, h.trie⟩

/-- The invariant depends only on the cells from b0 on, without the scratch strings WD, CUR, BOX,
SS. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Memory.lean (DSReady.congr)
theorem DSReadyP.congr (h : DSReadyP p t hmL aX aY b0 X Y μ)
    (he : ∀ a, b0 ≤ a → Outside (aWD p b0) (3 * p.L + p.m) a → μ' a = μ a) :
    DSReadyP p t hmL aX aY b0 X Y μ' := by
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  exact ⟨h.shared.congr fun a ha hlt _ => he a ha (by omega),
    by rw [he _ (by omega) (by omega)]; exact h.cellT,
    h.roots.congr fun i _ => he _ (by omega) (by omega),
    h.trie.congr fun i _ => he _ (by omega) (by omega)⟩

/-- A memory that differs from one that holds the data structure only on the scratch strings WD,
CUR, BOX, SS holds it too. -/
theorem DSReadyP.of_same (h : DSReadyP p t hmL aX aY b0 X Y μ)
    (hs : SameOutside μ μ' (aWD p b0) (3 * p.L + p.m)) : DSReadyP p t hmL aX aY b0 X Y μ' :=
  h.congr fun a _ ha => hs a ha

/-- The invariant of the data structure only depends on the cells from b0 on. -/
theorem dsReadyP_congr (h : DSReadyP p t hmL aX aY b0 X Y μ) (he : ∀ a, b0 ≤ a → μ' a = μ a) :
    DSReadyP p t hmL aX aY b0 X Y μ' :=
  h.congr fun a ha _ => he a ha

end

/-- The time of `preCoreP`; c is the constant of the pruned shared stage (`Sec2.SharedSpecP`). -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Memory.lean (tPreCore)
def tPreCoreP (c : ℕ) (p : Sec2.Par) (t : ℕ) : ℕ :=
  c * Sec2.sharedShapeP p + tAllTiles p.L p.m t p.nB + 300

/-- queryAt(I, J, b0) returns (XY)[I, J] from the block at b0, of which it changes only cells of the
scratch strings WD to SS: upstream's routine, with the encodings right at the leaves with at most
`m` symbols `P₀` only. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Memory.lean (QueryAtSpec)
def QueryAtSpecP (lim : Limits) (P : Program) : Prop :=
  ∀ (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (U : ℤ) (μ : ℕ → ℤ) (I J : Fin p.N),
    t ≤ p.m → Lim30 lim p t b0 U → (∀ i j, |X i j| ≤ U) → (∀ i j, |Y i j| ≤ U) →
    DSReadyP p t hmL aX aY b0 X Y μ →
    ∀ d, d + 2 ≤ lim.depth →
    Meets lim P Proc.queryAt d [(I : ℕ), (J : ℕ), b0] μ (tQueryAt p.L p.m t) fun r μ' =>
      r = (X * Y) I J ∧ DSReadyP p t hmL aX aY b0 X Y μ' ∧
        SameOutside μ μ' (aWD p b0) (3 * p.L + p.m)

/-- preCoreP(L, m, t, N, D, aX, aY, b0) builds the data structure for the matrices at aX and aY in
the block from b0 on, with the pruned encoder.  Nothing is assumed about the content of the
block. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Memory.lean (PreCoreSpec)
def PreCoreSpecP (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (U : ℤ) (μ : ℕ → ℤ),
    t ≤ p.m → Lim30 lim p t b0 U → (∀ i j, |X i j| ≤ U) → (∀ i j, |Y i j| ≤ U) →
    MatAt μ aX X → MatAt μ aY Y → aX + p.N * p.D ≤ b0 → aY + p.D * p.N ≤ b0 →
    ∀ d, d + (p.L + 6) ≤ lim.depth →
    Meets lim P Proc.preCoreP d [p.L, p.m, t, p.N, p.D, aX, aY, b0] μ
      (tPreCoreP c p t) fun _ μ' =>
      DSReadyP p t hmL aX aY b0 X Y μ' ∧ SameOutside μ μ' b0 (top p t b0 - b0)

/-! ## The directory, after the pruned shared stage -/

section

variable {p : Sec2.Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ : ℕ → ℤ}

/-- A cell of the directory. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Areas.lean (dir_cell)
theorem dir_cellP (h : Sec2.SharedReadyP p hmL aX aY b0 X Y μ) {j : ℕ} (hj : j < 31) :
    μ (b0 + j) = (((Sec2.dirList p aX aY b0).getD j 0 : ℕ) : ℤ) :=
  h.dir.read (by simpa [Sec2.dirList] using hj)

/-- Cell j of the directory, with the address in the form in which the evaluation of mem[b0 + j]
meets it. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/CellDependencies.lean
-- (SharedReady.dir_read)
theorem _root_.Light.Sec2.SharedReadyP.dir_read (h : Sec2.SharedReadyP p hmL aX aY b0 X Y μ)
    {j : ℕ} (hj : j < 31) :
    μ ((b0 : ℤ) + j).toNat = ((Sec2.dirList p aX aY b0).getD j 0 : ℕ) := by
  rw [toNat_natCast_add_natCast]
  exact dir_cellP h hj

/-- After the pruned shared stage the directory holds what `DirCells` says. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Directory.lean
-- (SharedReady.dirCells)
theorem _root_.Light.Sec2.SharedReadyP.dirCells (h : Sec2.SharedReadyP p hmL aX aY b0 X Y μ) :
    DirCells p b0 μ where
  levels := dir_cellP h (j := Dir.levels) (by norm_num)
  inner := dir_cellP h (j := Dir.inner) (by norm_num)
  outer := h.dir_read (j := Dir.outer) (by norm_num)
  blocks := h.dir_read (j := Dir.blocks) (by norm_num)
  bands := h.dir_read (j := Dir.bands) (by norm_num)
  leaves := h.dir_read (j := Dir.leaves) (by norm_num)
  mask := h.dir_read (j := Dir.mask) (by norm_num)
  band := h.dir_read (j := Dir.band) (by norm_num)
  block := h.dir_read (j := Dir.block) (by norm_num)
  digits := h.dir_read (j := Dir.digits) (by norm_num)
  encA := h.dir_read (j := Dir.encA) (by norm_num)
  encB := h.dir_read (j := Dir.encB) (by norm_num)
  sharedEnd := h.dir_read (j := Dir.sharedEnd) (by norm_num)

end

end Light.Sec4
