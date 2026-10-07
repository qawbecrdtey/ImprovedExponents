module

public import ThreeSumApsp

@[expose] public section

/-!
# The upstream formalization

This project builds on the Lean formalization of Alman and Vassilevska Williams, *Truly Subquadratic
3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs* (arXiv 2610.06783), published
as `anthropics/formal-math/3sum-apsp`. This file only checks that the dependency is in place.
-/

namespace ImprovedExponents

open ThreeSumApsp

/-- The paper's bound for 3SUM, as proved upstream about programs of the word RAM. -/
example : EndStatement.Theorem_22_3SUM :=
  wordRam_theorem_22_second.threeSum.endStatement (by norm_num) (by norm_num)

end ImprovedExponents
