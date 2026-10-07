module

public import ImprovedExponents.Statements

/-!
# The improved bounds: the proofs

This module imports the theorems of the same names and statements as those of
`ImprovedChallenge.lean` from the library (`ImprovedExponents/Statements.lean`) and adds nothing of
its own. Comparator (`comparator.json`) checks that each of the four has exactly the statement of
its namesake in `ImprovedChallenge.lean` and that its proof uses no axiom beyond `propext`,
`Quot.sound` and `Classical.choice`.
-/
