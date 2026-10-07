module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Offline
public import ImprovedExponents.PrunedProgram.Pre.Defs

@[expose] public section

/-!
# The time functions of the pruned offline routine

`tPre31P` and `tOffline32P` are upstream's `tPre31` and `tOffline32` (`ThreeSumApsp/Programs/Sec4/
ChoosingParameters/{Parameters,Offline}.lean`) with `tPreCoreP` in place of `tPreCore`: the only
change of the pruned solver's running time is the work of the encoder in the shared stage.  They
are fixed here so that the cost analysis (`ImprovedExponents.Cost8P`) and the routine
(`ImprovedExponents.PrunedProgram.Wrapper`) agree.

Adapted from upstream (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp

/-- The time of the pruned preprocessing `pre31P`; c is the constant of the pruned shared stage. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (tPre31)
def tPre31P (c : ℕ) (G : RatParams) (N D₀ : ℕ) : ℕ :=
  tLog4 (logFour D₀) + 30 +
    if logFour D₀ < G.m₀ then 0 else
      tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀))
        + tCopy (D₀ * N) + tFill ((D (logFour D₀) - D₀) * N)
        + tPreCoreP c (parOf G N D₀) (switchOf31 G D₀) + 120

/-- The time of the pruned offline routine `offline32P` on an instance with `w` wanted positions.
-/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (tOffline32)
def tOffline32P (c : ℕ) (G : RatParams) (N D₀ w : ℕ) : ℕ :=
  tPre31P c G N D₀ + w * (tQuery31 G D₀ + 30) + 20

end Light.Sec4
