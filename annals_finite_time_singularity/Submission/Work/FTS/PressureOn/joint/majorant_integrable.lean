import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.joint

/-- **The singular majorant of the Newtonian kernel is integrable.**

The function `z ↦ (4π)⁻¹ ‖z‖⁻²` restricted to the closed ball of radius `S` about the origin is
integrable: in `ℝ³` the singularity `‖z‖⁻²` is exactly at the integrability threshold
(`∫_{‖z‖≤S} ‖z‖⁻² dz = 4π S`), the extra `‖z‖²` in the volume element cancelling the `‖z‖⁻²`.

Proof.  The function is `(closedBall 0 S).indicator (fun z ↦ (4π)⁻¹‖z‖⁻²)`, so it suffices to
integrate the radial function over the closed ball.  Since `closedBall 0 S ⊆ ball 0 (S+1)`, it
suffices to integrate it over the *open* ball, where the polar-coordinate formula
`MeasureTheory.integrableOn_fun_norm_addHaar` applies: it converts integrability of
`x ↦ f ‖x‖` on `ball 0 r` into integrability of `y ↦ y ^ (finrank ℝ ℝ³ - 1) • f y` on
`Ioo 0 r`.  Here `finrank ℝ ℝ³ - 1 = 2`, and `y ^ 2 • ((4π)⁻¹ * (y^2)⁻¹) = (4π)⁻¹` for `y ≠ 0`,
i.e. the reduced integrand is (a.e.) the constant `(4π)⁻¹` on the bounded interval
`Ioo 0 (S+1)`. -/
theorem majorant_integrable (S : ℝ) :
    MeasureTheory.Integrable (fun z : R3 => (4 * Real.pi)⁻¹ * ((‖z‖ ^ 2)⁻¹ *
      (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) z)) MeasureTheory.volume := by
  -- The integrand is the indicator of the closed ball times the radial kernel.
  have hfun : (fun z : R3 => (4 * Real.pi)⁻¹ * ((‖z‖ ^ 2)⁻¹ *
        (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) z))
      = (Metric.closedBall (0 : R3) S).indicator
          (fun z : R3 => (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) := by
    funext z
    by_cases hz : z ∈ Metric.closedBall (0 : R3) S
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, mul_one]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero, mul_zero]
  rw [hfun, MeasureTheory.integrable_indicator_iff (Metric.isClosed_closedBall.measurableSet)]
  -- Integrability of the radial kernel on the open ball, via polar coordinates.
  have hball : MeasureTheory.IntegrableOn
      (fun z : R3 => (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) (Metric.ball 0 (S + 1))
      MeasureTheory.volume := by
    have hiff := MeasureTheory.integrableOn_fun_norm_addHaar
      (μ := (MeasureTheory.volume : MeasureTheory.Measure R3))
      (f := fun t : ℝ => (4 * Real.pi)⁻¹ * (t ^ 2)⁻¹) (r := S + 1)
    rw [hiff]
    -- The reduced integrand on `Ioo 0 (S+1)` is the constant `(4π)⁻¹`.
    have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (4 * Real.pi)⁻¹)
        (Set.Ioo 0 (S + 1)) MeasureTheory.volume :=
      MeasureTheory.integrableOn_const (hs := by simp [Real.volume_Ioo])
    refine hconst.congr_fun ?_ measurableSet_Ioo
    intro y hy
    simp only [smul_eq_mul]
    rw [show Module.finrank ℝ R3 - 1 = 2 from by simp [finrank_euclideanSpace]]
    field_simp
    rw [div_self hy.1.ne']
  exact hball.mono_set (fun z hz => by
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith [dist_nonneg (x := z) (y := (0 : R3))])

end Work.FTS.PressureOn.joint
