/-
The block from the documentation comment «Claims of the paper …» to the line «end EndStatement»
below is the file `EndStatement.lean` of the formalization anthropics/formal-math (directory
`3sum-apsp`, commit e1a4e6508154ea59f030480661590a9fe3018011), Copyright (c) 2026 Anthropic, PBC,
released under the Apache License 2.0 (see `NOTICE`), copied without any change;
`scripts/check-endstatement.sh` confirms this against the dependency. Everything after
`end EndStatement` is new.
-/
module

/-!
# The improved bounds for 3SUM, Exact Triangle, the (min,+)-product and APSP: the statements

This is the statement module that Comparator checks (`comparator.json`): the four strongest bounds
of the project, each with `sorry` in place of its proof, stated with nothing but the definitions of
this file. The module imports nothing, not even Mathlib. `ImprovedSolution.lean` imports the proofs
of the theorems of the same names from the library `ImprovedExponents`
(`ImprovedExponents/Statements.lean`).

**The first part**, the namespace `EndStatement`, is the trusted file of the Lean formalization of
the paper *Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided
Graphs* by Josh Alman and Virginia Vassilevska Williams (arXiv:2610.06783), copied verbatim from the
upstream formalization (see the comment at the top). It defines a word RAM (`Instr`, `exec`: nine
kinds of instruction, one step each, words of `W` bits, cells named by integers), what it means
that a problem is solved within a time bound, and the four problems:

* `Problem.SolvedInTime Q r`: for every exponent `κ` there are one program `P`, one slope `b` and
  one time bound `T(n) = O(n^r)` (`BigO`, both sides raised to the power `r.den`, since core Lean
  has no fractional powers) such that on every instance of every size `n` whose numbers have
  absolute value at most `n^κ`, and at every word size `W ≥ b (⌊log₂ n⌋ + 1)`, the program halts
  within `T(n)` steps with the right verdict (`yes`) and the right output (`output`)
  (`Problem.SolvedBy`). The program is deterministic; the input is written in the cells after `n`
  (`loadWords`), matrices row by row (`rowByRow`).
* `ThreeSum`: `n` integers; accept iff three of them, at three different positions, sum to `0`.
* `ExactTriangle`: three `n × n` weight matrices (a complete tripartite graph); accept iff some
  triangle has total weight `0`.
* `MinPlusProduct`: two `n × n` integer matrices; the output cells must hold their (min,+)-product.
* `APSP`: a directed graph on `n` vertices with integer weights, no negative cycle, as a matrix of
  edges and a matrix of weights; for each pair, the output cells must hold a flag and the distance.

The claims of that file (`Theorem_19`, `Theorem_22_3SUM`, `Theorem_22_MinPlus`, `Theorem_22_APSP`,
`Corollary_39_ZeroWeight`) are the bounds of the paper, proved upstream; they are not compared
here. Only the definitions are used.

**The second part** states the bounds of this project, in the same sense. The exponents are
rational numbers, written as decimal numerals (`1.99896 = 24987/12500`).

| theorem | problem | this project | the paper (proved upstream) |
|---|---|---|---|
| `threeSum_pruned` | 3SUM | `O(n^1.99896)` | `O(n^1.9992)` |
| `exactTriangle_pruned` | Exact Triangle | `O(n^2.99791)` | `O(n^(3 - 0.0017))` |
| `minPlus_allEdges_pruned` | (min,+)-product | `O(n^2.99791)` | `O(n^2.99942)` |
| `apsp_allEdges_pruned` | APSP | `O(n^2.99791)` | `O(n^2.99942)` |

None of the four theorems has a hypothesis. The constants hidden in `O(·)` are not optimized and
no value is given for them. Running times are counted in steps of the machine, each instruction one
step, at every word size at least `b (⌊log₂ n⌋ + 1)`; the model is generous in that cells need not
be addressable by a word and no space is charged (see `docs/MACHINE.md` of the upstream
formalization).
-/

/-! Claims of the paper «Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs» (Josh
Alman, Virginia Vassilevska Williams), about programs of a word RAM defined here. Imports nothing, proves nothing. -/

@[expose] public section

namespace EndStatement

/-- `i j k` name cells, `l` a position in the program, `[i]` is the word in cell `i`. The only constant is 1. -/
inductive Instr where
  | one (i : Int)             -- [i] := 1
  | add (i j k : Int)         -- [i] := [j] + [k]
  | sub (i j k : Int)         -- [i] := [j] - [k]
  | mul (i j k : Int)         -- [i] := [j] * [k]
  | load (i j : Int)          -- [i] := [[j]]
  | store (i j : Int)         -- [[i]] := [j]
  | bltz (i : Int) (l : Nat)  -- if [i] < 0, go to position l
  | accept
  | reject

/-- The verdict and the final memory, if `P`, run from position `pc` on memory `m`, halts within `t` steps, the halting
step counted; past its end `P` rejects. Addresses are read signed; `bltz` jumps on a negative word; `write` runs on. -/
def exec {W : Nat} (P : List Instr) : (t pc : Nat) → (m : Int → BitVec W) → Option (Bool × (Int → BitVec W))
  | 0, _, _ => none
  | t + 1, pc, m =>
    let write (i : Int) (v : BitVec W) := exec P t (pc + 1) fun x => if x = i then v else m x
    match P.getD pc .reject with
    | .one i => write i 1
    | .add i j k => write i (m j + m k)
    | .sub i j k => write i (m j - m k)
    | .mul i j k => write i (m j * m k)
    | .load i j => write i (m (m j).toInt)
    | .store i j => write (m i).toInt (m j)
    | .bltz i l => exec P t (if (m i).toInt < 0 then l else pc + 1) m
    | .accept => some (true, m)
    | .reject => some (false, m)

/-- The memory at the start: `ws` in cells 0, 1, 2, …, and 0 in every other cell. -/
def loadWords (W : Nat) (ws : List Int) : Int → BitVec W :=
  fun a => if a < 0 then 0 else BitVec.ofInt W (ws.getD a.toNat 0)

/-- `T(n) = O(n^r)`, both sides raised to the power `r.den`: core Lean has no fractional powers. For `r = 1.9992 =
2499/1250` it says `T(n)^1250 ≤ K n^2499`. -/
def BigO (T : Nat → Nat) (r : Rat) : Prop :=
  ∃ K : Nat, ∀ n ≥ 2, T n ^ r.den ≤ K * n ^ r.num.toNat

/-- `yes`: when to accept (always, if not given). `output`: a condition on the cells after the input, read as signed. -/
structure Problem where
  Instance : Nat → Type
  input {n : Nat} : Instance n → List Int
  yes {n : Nat} : Instance n → Prop := fun _ => True
  output {n : Nat} : Instance n → (Nat → Int) → Prop := fun _ _ => True

/-- One run: with `n` in cell 0 and the input after it, `P` halts within `t` steps with the right verdict and output. -/
def Problem.SolvedBy (Q : Problem) {n : Nat} (x : Q.Instance n) (P : List Instr) (W t : Nat) : Prop :=
  ∃ verdict m, exec P t 0 (loadWords W ((n : Int) :: Q.input x)) = some (verdict, m) ∧
    (verdict = true ↔ Q.yes x) ∧ Q.output x fun a => (m (1 + (Q.input x).length + a : Nat)).toInt

/-- Theorem 2: «a word RAM with O(log n)-bit words», «all numbers in the input are integers of absolute value
n^O(1)»: for every `κ`, one `P`, `b`, `T` for all instances, correct at every `W ≥ b(⌊log₂ n⌋ + 1)`. -/
def Problem.SolvedInTime (Q : Problem) (r : Rat) : Prop :=
  ∀ κ : Nat, ∃ (P : List Instr) (b : Nat) (T : Nat → Nat), BigO T r ∧
    ∀ (n : Nat) (x : Q.Instance n), (∀ a ∈ Q.input x, a.natAbs ≤ n ^ κ) → ∀ W ≥ b * (Nat.log2 n + 1),
      Q.SolvedBy x P W (T n)

def rowByRow {n : Nat} (w : Fin n → Fin n → Int) : List Int :=
  (List.ofFn fun u => List.ofFn fun v => w u v).flatten

/-- Section 3.2: «S(a, b, c) := w(a, b) + w(b, c) + w(a, c). A zero triangle is a triangle … with S(a, b, c) = 0». -/
def ExactTriangle : Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int) × (Fin n → Fin n → Int)
  input := fun (wAB, wBC, wAC) => rowByRow wAB ++ rowByRow wBC ++ rowByRow wAC
  yes := fun (wAB, wBC, wAC) => ∃ a b c, wAB a b + wBC b c + wAC a c = 0

/-- Theorem 19: «ε_T := 0.0017». -/
def ε_T : Rat := 0.0017

/-- Theorem 19: «Exact Triangle … can be solved by a deterministic algorithm in … O(n^(3−ε_T)) time». -/
def Theorem_19 : Prop :=
  ExactTriangle.SolvedInTime (3 - ε_T)

/-- Section 1: «Given n numbers, decide whether three of them sum to 0». Three different positions. -/
def ThreeSum : Problem where
  Instance n := Fin n → Int
  input x := List.ofFn x
  yes x := ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i + x j + x k = 0

/-- Theorem 22: «solve 3SUM on n integers of absolute value at most n^ν», in time «O(n^1.9992)». -/
def Theorem_22_3SUM : Prop :=
  ThreeSum.SolvedInTime 1.9992

/-- Output, row by row: entry `(i, j)` is the least of the sums `A i k + B k j`. -/
def MinPlusProduct : Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int)
  input := fun (A, B) => rowByRow A ++ rowByRow B
  output := fun {n} (A, B) out => ∀ i j : Fin n,
    (∃ k, out (i.val * n + j.val) = A i k + B k j) ∧ ∀ k, out (i.val * n + j.val) ≤ A i k + B k j

/-- Theorem 22: «the (min, +)-product of two n × n integer matrices», in time «O(n^2.99942)». -/
def Theorem_22_MinPlus : Prop :=
  MinPlusProduct.SolvedInTime 2.99942

/-- A path and its total weight; it may repeat vertices. -/
inductive Path {n : Nat} (w : Fin n → Fin n → Option Int) : Fin n → Fin n → Int → Prop
  | nil (i : Fin n) : Path w i i 0
  | cons {i j k : Fin n} {d e : Int} : w i j = some d → Path w j k e → Path w i k (d + e)

/-- Input: the 0/1 matrix of the edges, then the weights, with 0 for no edge. Output, two cells for each `(i, j)`: 1 if
there is a path, else 0; then the distance. -/
def APSP : Problem where
  Instance n := {w : Fin n → Fin n → Option Int // ∀ i d, Path w i i d → 0 ≤ d}
  input := fun ⟨w, _⟩ => rowByRow (fun i j => if (w i j).isSome then 1 else 0) ++ rowByRow fun i j => (w i j).getD 0
  output := fun {n} ⟨w, _⟩ out => ∀ i j : Fin n,
    let flag := out (2 * (i.val * n + j.val))
    let dist := out (2 * (i.val * n + j.val) + 1)
    (flag = 1 ∧ Path w i j dist ∧ ∀ e, Path w i j e → dist ≤ e) ∨ (flag = 0 ∧ ∀ e, ¬ Path w i j e)

/-- Theorem 22: «APSP on directed n-vertex graphs … and no negative cycles», in time «O(n^2.99942)». -/
def Theorem_22_APSP : Prop :=
  APSP.SolvedInTime 2.99942

/-- `w i j u v`: weight between `u` in part `i` and `v` in part `j`. All `k²` blocks are input; only `i < j` counts. -/
def ZeroWeightKClique (k : Nat) : Problem where
  Instance n := Fin k → Fin k → Fin n → Fin n → Int
  input w := (List.ofFn fun i => (List.ofFn fun j => rowByRow (w i j)).flatten).flatten
  yes {n} w := ∃ v : Fin k → Fin n,
    (List.ofFn fun j => (List.ofFn fun i => if i < j then w i j (v i) (v j) else 0).sum).sum = 0

/-- Corollary 39: «decide in O(n^(k−ε_T⌊k/3⌋)) time whether some k-clique … has total edge weight zero». -/
def Corollary_39_ZeroWeight : Prop :=
  ∀ k ≥ 3, (ZeroWeightKClique k).SolvedInTime (k - ε_T * (k / 3 : Nat))

end EndStatement

namespace ImprovedExponents

/-- **3SUM in `O(n^1.99896)` steps on the word RAM.** The paper has `O(n^1.9992)`. The algorithm is
the paper's, with the exact count of the leaves of its recursion, the reduction from Exact
Triangle charged at the true size of the middle part, and encodings restricted to the leaves that
are read. -/
theorem threeSum_pruned : EndStatement.ThreeSum.SolvedInTime 1.99896 := by
  sorry

/-- **Exact Triangle in `O(n^2.99791)` steps on the word RAM.** The paper has `O(n^(3 - 0.0017))`;
3SUM keeps half of the saving (`threeSum_pruned`). -/
theorem exactTriangle_pruned : EndStatement.ExactTriangle.SolvedInTime 2.99791 := by
  sorry

/-- **The (min,+)-product in `O(n^2.99791)` steps on the word RAM.** The paper has `O(n^2.99942)`,
a third of its saving for Exact Triangle; here the whole saving is kept, through the all-edges
version of Exact Triangle (footnote 10 of the paper). -/
theorem minPlus_allEdges_pruned : EndStatement.MinPlusProduct.SolvedInTime 2.99791 := by
  sorry

/-- **APSP in `O(n^2.99791)` steps on the word RAM**, for directed graphs with integer weights and
no negative cycle. The paper has `O(n^2.99942)`; the whole saving is kept, as for the
(min,+)-product. -/
theorem apsp_allEdges_pruned : EndStatement.APSP.SolvedInTime 2.99791 := by
  sorry

end ImprovedExponents
