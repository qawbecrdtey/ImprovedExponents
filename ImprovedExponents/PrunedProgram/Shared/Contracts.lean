module

public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ImprovedExponents.PrunedProgram.SegOn
public import ImprovedExponents.PrunedProgram.Work
public import ImprovedExponents.PrunedProgram.Procs

@[expose] public section

/-!
# The shared stage with the pruned encoder: what it leaves behind, its shape and its specification

Upstream's shared stage (`Light.Sec2.sharedBody`, `Light.Sec2.SharedSpec`) leaves the tables, the
directory and the encodings of all bands as full segments (`SharedReady`).  With the pruned encoder
the encodings are right at the leaves with at most `m` symbols `P₀` only (`SharedReadyP`, with
`SegOn` in place of `Seg`), and the shape of the running time has the work `encWorkP L m` of the
pruned encoder in place of the `10^L` cells of a full encoding (`sharedShapeP`).  Everything else
is as upstream.  This file fixes the interface between the stage (`PrunedProgram.Shared.Stage`)
and its consumers (`PrunedProgram.Pre`).

Adapted from upstream `ThreeSumApsp/Programs/Sec2/Theorem5/Contracts.lean` and
`CellDependencies.lean` (Apache-2.0).
-/

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- What the pruned shared stage leaves behind: the tables, the directory, and the encodings of all
bands at the leaves with at most `m` symbols `P₀`.  (Cell 31 of the directory is not used by
it.) -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Contracts.lean (SharedReady)
structure SharedReadyP (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (μ : ℕ → ℤ) : Prop
  extends SharedTables p b0 μ where
  dir : SegN μ (p.aDIR b0) (dirList p aX aY b0)
  encA : ∀ β < p.nB, SegOn p.m μ (p.aENCA b0 + β * p.T)
    (encodingL (bandArrayL (Spec.stdLayout hmL) X β))
  encB : ∀ β < p.nB, SegOn p.m μ (p.aENCB b0 + β * p.T)
    (encodingR (bandArrayR (Spec.stdLayout hmL) Y β))

/-- Full encodings are in particular right at the leaves with few symbols `P₀`. -/
theorem SharedReady.toP (h : SharedReady p hmL aX aY b0 X Y μ) :
    SharedReadyP p hmL aX aY b0 X Y μ :=
  { h.toSharedTables with
    dir := h.dir
    encA := fun β hβ => .of_seg (h.encA β hβ)
    encB := fun β hβ => .of_seg (h.encB β hβ) }

/-- What the pruned shared stage leaves behind is kept by a memory that agrees on the cells of the
shared block, but for cell 31 of the directory, which the shared stage does not use. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/CellDependencies.lean
-- (SharedReady.congr)
theorem SharedReadyP.congr (h : SharedReadyP p hmL aX aY b0 X Y μ)
    (hag : ∀ a, b0 ≤ a → a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReadyP p hmL aX aY b0 X Y μ' := by
  have hplaces := p.places b0
  have tb : SharedTables p b0 μ' :=
    h.toSharedTables.congr fun x hlo hx => hag x (by omega) (by omega) (by omega)
  have henc : ∀ {a β i : ℕ}, p.aENCA b0 ≤ a → a + p.nB * p.T ≤ p.sharedEnd b0 → β < p.nB →
      i < p.T → μ' (a + β * p.T + i) = μ (a + β * p.T + i) := fun ha hend hβ hi => by
    have := Nat.mul_add_lt_mul hβ hi
    exact hag _ (by omega) (by omega) (by omega)
  have hT : p.T = 10 ^ p.L := rfl
  refine
    { tb with
      dir := h.dir.congr fun i hi => ?_
      encA := fun β hβ => (h.encA β hβ).congr fun i hi => henc le_rfl (by omega) hβ (hT ▸ hi)
      encB := fun β hβ => (h.encB β hβ).congr fun i hi =>
        henc (by omega) (by omega) hβ (hT ▸ hi) }
  simp only [dirList, List.length_map, List.length_cons, List.length_nil] at hi
  simp only [Par.aDIR]
  exact hag _ (by omega) (by omega) (by omega)

/-- What the pruned shared stage leaves behind is kept by a memory that agrees on all cells below
the end of the shared block, but for cell 31 of the directory. -/
theorem SharedReadyP.of_agree (h : SharedReadyP p hmL aX aY b0 X Y μ)
    (hag : ∀ a, a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReadyP p hmL aX aY b0 X Y μ' :=
  h.congr fun a _ => hag a

/-- The shape of the running time of the pruned shared stage: upstream's `sharedShape` with the
work `encWorkP L m` of the pruned encoder in place of the `10^L` cells of a full encoding. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Contracts.lean (sharedShape)
def sharedShapeP (p : Par) : ℕ :=
  (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1) + (p.N + 1) * (p.Lo + 1)
    + (p.D + 1) * (p.m + 1)
    + p.nB * (encWorkP p.L p.m + bandArrayShape p)

/-- sharedP(L, m, N, D, aX, aY, b0): fills the shared block, with the encodings right at the leaves
with at most `m` symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Contracts.lean (SharedSpec)
def SharedSpecP (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ),
    SharedPre lim p aX aY b0 X Y V μ →
    ∀ d, d + (p.L + 3) ≤ lim.depth →
    Meets lim P Proc.sharedP d [p.L, p.m, p.N, p.D, aX, aY, b0] μ (c * sharedShapeP p) fun _ μ' =>
      SharedReadyP p hmL aX aY b0 X Y μ' ∧ SameOutside μ μ' b0 (p.sharedEnd b0 - b0)

end Light.Sec2
