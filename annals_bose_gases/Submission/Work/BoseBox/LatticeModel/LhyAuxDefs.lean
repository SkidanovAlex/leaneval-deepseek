import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseBox.LatticeModel.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary functions for the Lipschitz estimate on `lhyProfile`

`lhyProfile c` (see `Submission.Work.BoseBox.LatticeModel.Defs`) is, on `(0,∞)`,
equal to the elementary expression

`lhyF c r = r² + c − r·√(r²+2c) − c²/(2r²)`

(the rationalisation `c²/((r²+c)+r√(r²+2c)) = (r²+c) − r√(r²+2c)` uses
`(r²+c)² − r²(r²+2c) = c²`).  The point of the rewrite is that `lhyF c` is
differentiable on `(0,∞)` with the explicit derivative

`lhyD c r = 2r − 2(r²+c)/√(r²+2c) + c²/r³`,

which satisfies `0 ≤ lhyD c r ≤ c²/r³`.
-/

noncomputable section

open scoped Real

namespace Work.BoseBox.LatticeModel

/-- The rationalised (algebraic) form of the Bogoliubov bracket, equal to
`lhyProfile c r` for `r > 0`. -/
noncomputable def lhyF (c r : ℝ) : ℝ :=
  r ^ 2 + c - r * Real.sqrt (r ^ 2 + 2 * c) - c ^ 2 / (2 * r ^ 2)

/-- The derivative of `lhyF c` on `(0,∞)`. -/
noncomputable def lhyD (c r : ℝ) : ℝ :=
  2 * r - 2 * (r ^ 2 + c) / Real.sqrt (r ^ 2 + 2 * c) + c ^ 2 / r ^ 3

end Work.BoseBox.LatticeModel
