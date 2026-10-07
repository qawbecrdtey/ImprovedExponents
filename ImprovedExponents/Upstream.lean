module

public import ThreeSumApsp.RunningTimes.Sec3.Theorem22
public import ThreeSumApsp.Statements.Exponents

@[expose] public section

/-!
# The upstream formalization

This project builds on the Lean formalization of Alman and Vassilevska Williams, *Truly Subquadratic
3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs* (arXiv 2610.06783), published
as `anthropics/formal-math/3sum-apsp`; the part of it that this project uses is included in
`upstream/3sum-apsp/` and ported to Lean `v4.35.0-rc2` (`upstream/README.md`). This file only checks
that it is in place.
-/

namespace ImprovedExponents

open ThreeSumApsp

/-- The paper's bound for 3SUM, as proved upstream about programs of the word RAM. -/
example : EndStatement.Theorem_22_3SUM :=
  wordRam_theorem_22_second.threeSum.endStatement (by norm_num) (by norm_num)

end ImprovedExponents
