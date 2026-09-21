import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddEnvelope.Defs

/-!
# The gluing cutoff of the odd-window construction

This file defines the single auxiliary function used to glue the window solution `Z` of the
odd-dimensional Volterra system onto the semicircle chord function `profileX` on `(0, 1/2)`.

The function `gluePsi` is a smooth function of the slope `s ≥ 0` which

* equals `1` at `0` (so that `s ↦ Z (gluePsi s) 0` tends to `Z 1 0 = profileX 1` at `0⁺`),
* equals the identity for `s ≥ 1/2` (so that on `[1/2, ∞)` it reproduces `Z` exactly),
* stays strictly above `1/4` (so that the estimates available for `Z` on `[1/4, ∞)` apply),
* is `≥ 9/10` for `s ≤ 1/50` (so that on this initial piece no estimate on `Z` is needed
  at all, because `Z` agrees with `BaseState` for arguments `≥ 9/10`),
* and satisfies the second-order bound
  `(ψ')² + (9/10 - ψ) |ψ''| ≤ 9` whenever `ψ < 9/10`, which is exactly what is needed to
  transfer the `1/1000`-bounds on `Z` into `1/100`-bounds on the glued curve.

All assertions about `gluePsi` are collected in `gluePsi_props`.
-/

namespace Work.OddVolterra.Existence

open scoped Topology

noncomputable section

/-- The argument-gluing function `ψ` of the odd window construction.  For `s < 1/2` it is given by
`s + (1 - s) * exp (-(6/5) * s / (1/2 - s))`, and it equals `s` for `s ≥ 1/2`. -/
noncomputable def gluePsi (s : ℝ) : ℝ :=
  s + (1 - s) * Real.exp (6 / 5) * expNegInvGlue ((5 / 3) * (1 / 2 - s))

/-- The deviation of the first component of a window solution from the semicircle chord
function. -/
noncomputable def devZero (Z : ℝ → Work.OddVolterra.St) (s : ℝ) : ℝ :=
  Z s 0 - Commons.Geometry.Ulam.profileX s

/-- The deviation of the second component of a window solution from the semicircle chord
function. -/
noncomputable def devOne (Z : ℝ → Work.OddVolterra.St) (s : ℝ) : ℝ :=
  Z s 1 - Commons.Geometry.Ulam.profileX s

end

end Work.OddVolterra.Existence
