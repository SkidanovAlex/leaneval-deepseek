import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the smooth cutoff `Work.Diff.C.cutoff_psi`

We construct the transition profile `cutW : ℝ → ℝ` and the rescaled profile `cutRho`, and the
candidate cutoff `cutPsi`, used in `Submission/Work/Diff/C/cutoff_psi.lean`.

* `cutW u = 0` for `u ≤ 0`, `cutW u = 1` for `1 ≤ u`, `0 ≤ cutW u ≤ 3/2`, and
  `∫ u in 0..1, cutW u = 1`;
* `cutRho c x = cutW ((x + 1 - c)/c)`;
* `cutPsi c s = (-1 + c) + ∫ x in (-1+c)..s, cutRho c x`.
-/

namespace Work.Diff.C

open MeasureTheory

/-- The transition profile: `0` on `(-∞,0]`, `1` on `[1,∞)`, of integral `1` over `[0,1]`. -/
noncomputable def cutW (u : ℝ) : ℝ :=
  (3 / 2) * Real.smoothTransition (2 * u) - (1 / 2) * Real.smoothTransition (2 * u - 1)

/-- The rescaled transition profile, concentrated on the interval `[-1+c, -1+2c]`. -/
noncomputable def cutRho (c : ℝ) (x : ℝ) : ℝ := cutW ((x + 1 - c) / c)

/-- The candidate cutoff function: constant `-1+c` on `(-∞,-1+c]` and the identity on
`[-1+2c,∞)`. -/
noncomputable def cutPsi (c : ℝ) (s : ℝ) : ℝ :=
  (-1 + c) + ∫ x in (-1 + c)..s, cutRho c x

end Work.Diff.C
