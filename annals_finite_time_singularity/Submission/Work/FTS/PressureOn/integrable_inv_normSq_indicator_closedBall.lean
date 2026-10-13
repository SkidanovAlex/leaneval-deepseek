import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Metric
open scoped Topology ENNReal

namespace Work.FTS.PressureOn

/-- In `ℝ³` the function `z ↦ ‖z‖⁻²` is integrable on any ball centred at the origin: the
angular average supplies the factor `r²` that makes `r⁻²` integrable against `dr` in dimension
`3`.  Formally this is the polar-coordinate identity
`MeasureTheory.integrable_fun_norm_addHaar`, which reduces integrability of `f ‖·‖` on `ℝ³` to
integrability of `y ↦ y² * f y` on `(0, ∞)`; for `f y = y⁻² 𝟙_{y ≤ S}` the latter is the
indicator of the finite interval `(0, S]`.  The value `S ≤ 0` is covered as well, the ball then
being null. -/
theorem integrable_inv_normSq_indicator_closedBall (S : ℝ) :
    MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 => (‖z‖ ^ 2)⁻¹ *
      (Metric.closedBall (0 : Work.FTS.PressureOn.R3) S).indicator (fun _ => (1 : ℝ)) z)
      MeasureTheory.volume := by
  -- Step 1: write the integrand as a function of the norm.
  have hEq : (fun z : Work.FTS.PressureOn.R3 => (‖z‖ ^ 2)⁻¹ *
        (Metric.closedBall (0 : Work.FTS.PressureOn.R3) S).indicator (fun _ => (1 : ℝ)) z)
      = fun z : Work.FTS.PressureOn.R3 =>
          (fun y : ℝ => (y ^ 2)⁻¹ * (Set.Iic S).indicator (fun _ => (1 : ℝ)) y) ‖z‖ := by
    funext z
    by_cases h : ‖z‖ ≤ S
    · have hz : z ∈ Metric.closedBall (0 : Work.FTS.PressureOn.R3) S := by
        simpa using h
      simp [hz, h]
    · have hz : z ∉ Metric.closedBall (0 : Work.FTS.PressureOn.R3) S := by
        simpa using h
      simp [hz, h]
  rw [hEq]
  -- Step 2: polar coordinates.
  refine (MeasureTheory.integrable_fun_norm_addHaar (μ := MeasureTheory.volume)
    (f := fun y : ℝ => (y ^ 2)⁻¹ * (Set.Iic S).indicator (fun _ => (1 : ℝ)) y)).mpr ?_
  have hdim : Module.finrank ℝ Work.FTS.PressureOn.R3 = 3 := by simp [Work.FTS.PressureOn.R3]
  -- On `(0, ∞)` the radial weight `y ^ (finrank - 1) = y²` cancels the `y⁻²`.
  have h1 : ∀ y ∈ Set.Ioi (0:ℝ),
      y ^ (Module.finrank ℝ Work.FTS.PressureOn.R3 - 1) •
        ((y ^ 2)⁻¹ * (Set.Iic S).indicator (fun _ => (1 : ℝ)) y)
      = (Set.Iic S).indicator (fun _ => (1 : ℝ)) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    rw [hdim]
    norm_num
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hy0), one_mul]
  rw [MeasureTheory.integrableOn_congr_fun h1 measurableSet_Ioi]
  -- Step 3: `𝟙_{(0,S]}` is integrable, the interval having finite measure.
  have h2 : (Set.Ioi (0:ℝ)).indicator ((Set.Iic S).indicator (fun _ => (1:ℝ)))
      = (Set.Ioc (0:ℝ) S).indicator (fun _ => (1:ℝ)) := by
    ext y
    by_cases hy : y ∈ Set.Ioi (0:ℝ) <;> by_cases hS : y ∈ Set.Iic S <;>
      simp_all [Set.mem_Ioc, Set.mem_Ioi, Set.mem_Iic]
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi, h2,
      MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
  exact MeasureTheory.integrableOn_const (by simp)

end Work.FTS.PressureOn
