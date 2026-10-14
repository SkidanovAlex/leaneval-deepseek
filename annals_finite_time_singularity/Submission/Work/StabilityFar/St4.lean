import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.LWP.Main
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.StabilityFar.Decay.timeDeriv_timeHolder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

open MeasureTheory

set_option linter.unusedVariables false

/-! ## The far-field bound on the difference of two time slices of `BS(∂ₜω)` -/


/-! ## The target: the far-field time-Hölder bound for `∂ₜu` -/


end Work.StabilityFar.Decay
end
-- ===== merged: Submission.Work.StabilityFar.St4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-- The far radius used in `St4`: `2R + 5`.  The slack of `5` makes the `Lipschitz`-on-a-ball
form of the Biot–Savart estimates (`ball x (‖x‖/4)`) and the segment bounds available at every
point of the far region, and keeps the far region inside `{2R < ‖x‖}` where the decay estimates
hold. -/
def st4Radius (R : ℝ) : ℝ := 2 * R + 5

/-! ## `fderiv u.uncurry` on the far region is the block derivative -/



/-! ## `α`-Hölder from a local `α`-Hölder bound and a global bound -/

/-- **A function that is `α`-Hölder on scales `≤ 1` and bounded is `α`-Hölder.**  This is the form
of the interpolation actually produced by the far-field estimates: the blocks of
`fderiv u.uncurry` satisfy an `α`-power estimate at small scales (their `t`-variation is
`α`-Hölder, with exponent `α`, not Lipschitz), and the decay estimates bound them globally. -/
theorem holderOnWith_of_local_holder_bounded {X Y : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] {α : NNReal} {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    {f : X → Y} {s : Set X}
    (hlocal : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 1 → ‖f x - f y‖ ≤ L * dist x y ^ (α : ℝ))
    (hbdd : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ 2 * B) :
    HolderOnWith (Real.toNNReal (max L (2 * B))) α f s := by
  refine Holder.holderOnWith_of_norm_le (C := Real.toNNReal (max L (2 * B))) (fun x hx y hy => ?_)
  have hC : ((Real.toNNReal (max L (2 * B)) : NNReal) : ℝ) = max L (2 * B) :=
    Real.coe_toNNReal _ (by positivity)
  rw [hC]
  rcases lt_or_ge (dist x y) 1 with hd | hd
  · exact le_trans (hlocal x hx y hy hd.le)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  · have h1 : (1 : ℝ) ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow hd α.coe_nonneg
    have h2 : 0 ≤ max L (2 * B) := by positivity
    calc ‖f x - f y‖ ≤ 2 * B := hbdd x hx y hy
      _ ≤ max L (2 * B) := le_max_right _ _
      _ = max L (2 * B) * 1 := by ring
      _ ≤ max L (2 * B) * dist x y ^ (α : ℝ) := mul_le_mul_of_nonneg_left h1 h2

/-! ## The main theorem -/


end Work.StabilityFar
end
