/-
# `Work.CoreResiduals.BiotSavart.KfBall.integrableOn_kf_ball` — local integrability of the
Newtonian kernel `b ↦ ‖b‖⁻³ • b` on a ball

The Biot–Savart kernel `kf b = ‖b‖⁻³ • b` has `‖kf b‖ = ‖b‖⁻²`, so its singularity at the
origin is of order `2`, which is below the critical order `dim = 3` of `ℝ³`.  Hence `kf` is
locally integrable, and in particular integrable on every ball `B(z,ρ)`.

The statement is an instance of the general layer-cake estimate
`MeasureTheory.integrableOn_ball_of_norm_le_rpow` (a function dominated by
`C ‖x‖ ^ (-α)` with `α < finrank ℝ E` is integrable on `ball 0 r`): we apply it with
`C = 1`, `α = 2`, `finrank ℝ ℝ³ = 3`, and the dominating function `‖·‖⁻²` supplied by
`Work.CoreResiduals.BiotSavart.norm_kf_eq`.  The ball `B(z,ρ)` is contained in the ball
`B(0, ‖z‖ + ρ)` around the origin, so a final `IntegrableOn.mono_set` transfers the
integrability to the shifted centre.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter
open scoped Topology

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart.KfBall

theorem integrableOn_kf_ball (z : Work.LWP.R3) (ρ : ℝ) :
    MeasureTheory.IntegrableOn (Work.StabilityFar.Decay.kf) (Metric.ball z ρ) := by
  -- `kf` is Borel measurable (it is `b ↦ (‖b‖³)⁻¹ • b`).
  have hmeas : MeasureTheory.AEStronglyMeasurable Work.StabilityFar.Decay.kf
      (volume : Measure Work.LWP.R3) := by
    unfold Work.StabilityFar.Decay.kf
    measurability
  have hfin : Module.finrank ℝ Work.LWP.R3 = 3 := by
    simp [Work.LWP.R3, finrank_euclideanSpace]
  -- Local integrability around the origin via the `2 < 3` layer-cake bound.
  refine (MeasureTheory.integrableOn_ball_of_norm_le_rpow
      (μ := (volume : Measure Work.LWP.R3))
      (f := Work.StabilityFar.Decay.kf) (C := 1) (α := 2) (r := ‖z‖ + ρ)
      ?_ ?_ ?_ hmeas).mono_set ?_
  · -- `1 ≤ finrank ℝ ℝ³`
    rw [hfin]; norm_num
  · -- `2 < finrank ℝ ℝ³`
    rw [hfin]; norm_num
  · -- `‖kf x‖ ≤ 1 * ‖x‖^(-2)`
    filter_upwards with x
    rw [Work.CoreResiduals.BiotSavart.norm_kf_eq x]
    simp
  · -- `B(z,ρ) ⊆ B(0, ‖z‖ + ρ)`
    intro a ha
    rw [Metric.mem_ball] at ha ⊢
    have h1 : dist a 0 ≤ dist a z + dist z 0 := dist_triangle a z 0
    rw [dist_zero_right, dist_zero_right] at h1
    rw [dist_zero_right]
    linarith

end Work.CoreResiduals.BiotSavart.KfBall
