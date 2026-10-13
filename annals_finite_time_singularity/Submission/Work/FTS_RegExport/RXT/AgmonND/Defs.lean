import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Topology.Algebra.Ring.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted radial Agmon inequality without a decay hypothesis: definitions

This file sets up the objects used in the proof of the *no-decay* weighted radial Agmon
inequality `Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay`, which is the statement of
`Work.FTS_RegExport.RXA1w.agmonZ_weight` with the hypothesis `x (v x w x)² → 0` removed:
that hypothesis is not needed, since integrability of `(v w)²` alone forces
`x (v x w x)²` to take arbitrarily small values along a sequence tending to `∞` (see
`Work.FTS_RegExport.RXT.small_value`), which is all the fundamental-theorem-of-calculus
argument requires.

With `w(x) = (1+x)²/x²` we have `(x (v x w x)²)' = -[4 (v x w x)² + (x v' w)²] + (error)`
with an error of a sign that only helps, so
`z (v z w z)² ≤ ∫_{z}^{∞} [4 (v w)² + (x v' w)²]`.

## Main definitions

* `agmonF v x = x * (v x * w x)²`, the quantity whose derivative is taken;
* `agmonFderiv v v' x = 2 v x (x v' x) w x² + (v x)² w x² ((x-3)/(1+x))`, the pointwise
  derivative of `agmonF v` at `x` (for `v'` a derivative of `v`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

/-- The radial weight `w` is continuous on `(0,∞)`. -/
lemma continuousOn_w_Ioi : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
  have h : (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) = Work.Spaces.w := by
    funext y; rw [Work.Spaces.w]
  rw [← h]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun y hy => pow_ne_zero 2 (ne_of_gt hy))

/-- `x * (v x * w x)²`, the weighted square of a radial slice. -/
def agmonF (v : ℝ → ℝ) (x : ℝ) : ℝ := x * (v x * Work.Spaces.w x) ^ 2

/-- A formula for the pointwise derivative of `agmonF v` on `(0,∞)`, when `v'` is a
pointwise derivative of `v` there. -/
def agmonFderiv (v v' : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2
    + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))

/-- `agmonF v` at a point, in the form appearing in the Agmon inequality. -/
lemma agmonF_eq (v : ℝ → ℝ) (x : ℝ) :
    agmonF v x = (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * x := by
  rw [agmonF]; ring

end Work.FTS_RegExport.RXT
