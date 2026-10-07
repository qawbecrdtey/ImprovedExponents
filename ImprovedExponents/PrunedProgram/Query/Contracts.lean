module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts
public import ImprovedExponents.PrunedProgram.SegOn

@[expose] public section

/-!
# The specification of `queryCore` on pruned encodings

Upstream's `queryCore` (procedure 53) assumes the two encodings of the tile as full segments
(`QueryCorePre.segA/segB : Seg μ aA (arrT encA)`).  It reads them at the leaves of order below `t`
contributing to the output string only, and such a leaf has at most `m` symbols `P₀`
(`card_P0Levels_le_of_contributes`, with `QueryCorePre.card`).  `QueryCorePreP` is `QueryCorePre`
with `SegOn m` in place of `Seg` in these two fields, and `QueryCoreSpecP` is `QueryCoreSpec` with
this weaker assumption; the routine and its time are upstream's.  `QueryCorePre.toP` says that the
full assumption implies the weaker one, and `segOn_of_same` that the two scratch strings of the
routine do not disturb a pruned encoding.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-- What `queryCore` assumes when the encodings are right at the leaves with at most `m` symbols
`P₀` only: upstream's `QueryCorePre` with `SegOn x.m` in place of `Seg` for the two encodings. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean (QueryCorePre)
structure QueryCorePreP (lim : Limits) (μ : ℕ → ℤ) (x : QueryCoreArgs) : Prop where
  std : Std lim
  t_le : x.t ≤ x.m
  card : (innerSetO x.η).card = x.m
  segA : SegOn x.m μ x.aA x.encA
  segB : SegOn x.m μ x.aB x.encB
  segT : Seg μ x.tr x.T
  segDigits : SegN μ x.wd (digitsO x.η)
  walk : ∀ l ∈ boxesOf x.m x.t (digitsO x.η), WalkOK x.T x.root l
  sums : ∀ j, |(x.terms.take j).sum| ≤ lim.word
  prod : ∀ τ, |x.encA τ * x.encB τ| ≤ lim.word
  pow : (10 : ℤ) ^ x.L ≤ lim.word
  ss_wd : Apart x.ss x.m x.wd x.L
  box_wd : Apart x.box x.L x.wd x.L
  ss_box : Apart x.ss x.m x.box x.L
  ss_aA : Apart x.ss x.m x.aA (10 ^ x.L)
  ss_aB : Apart x.ss x.m x.aB (10 ^ x.L)
  box_aA : Apart x.box x.L x.aA (10 ^ x.L)
  box_aB : Apart x.box x.L x.aB (10 ^ x.L)
  ss_tr : Apart x.ss x.m x.tr x.T.length
  box_tr : Apart x.box x.L x.tr x.T.length
  aA_lt : x.aA + 10 ^ x.L < lim.space
  aB_lt : x.aB + 10 ^ x.L < lim.space
  tr_lt : x.tr + x.T.length < lim.space
  wd_lt : x.wd + x.L < lim.space
  ss_lt : x.ss + x.m < lim.space
  box_lt : x.box + x.L < lim.space

/-- `queryCore` returns the sum `trieQuery` for the output string whose digits are at wd, when the
two encodings are right at the leaves with at most `m` symbols `P₀` only; it changes only the two
scratch strings.  Same procedure number and time as upstream. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean (QueryCoreSpec)
def QueryCoreSpecP (lim : Limits) (P : Program) : Prop :=
  ∀ (x : QueryCoreArgs) (μ : ℕ → ℤ), QueryCorePreP lim μ x →
    ∀ d, d + 1 ≤ lim.depth →
    Meets lim P Proc.queryCore d [x.aA, x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L, x.m, x.t] μ
      (tQueryCore x.L x.m x.t) fun r μ' =>
        r = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) ∧
          SameOutside2 μ μ' x.ss x.m x.box x.L

variable {lim : Limits} {μ μ₁ : ℕ → ℤ} {x : QueryCoreArgs}

/-- Full encodings are in particular right at the leaves with few symbols `P₀`. -/
theorem QueryCorePre.toP (C : QueryCorePre lim μ x) : QueryCorePreP lim μ x :=
  { C with segA := .of_seg C.segA, segB := .of_seg C.segB }

/-- A pruned encoding that meets neither scratch string is kept. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.seg_of_same)
theorem segOn_of_same {ss m box L a k L' : ℕ} {enc : Leaf L' → ℤ}
    (h : SameOutside2 μ μ₁ ss m box L) (hl : SegOn k μ a enc)
    (h1 : Apart ss m a (10 ^ L')) (h2 : Apart box L a (10 ^ L')) : SegOn k μ₁ a enc :=
  hl.congr fun i hi => h _ ⟨by omega, by omega⟩

end Light.Sec4
