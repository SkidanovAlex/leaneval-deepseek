/-
# The angular second moment of the unit sphere in `ℝ³` vanishes

This file proves

`∫_{S²} (id - 3 ω ⊗ ω) dσ(ω) = 0`

for the surface measure `σ = volume.toSphere` on the unit sphere of `ℝ³`
(`Work.LWP.R3 = EuclideanSpace ℝ (Fin 3)`), as an identity in the space of
continuous linear maps `ℝ³ →L[ℝ] ℝ³`.  Equivalently
`∫_{S²} ω ⊗ ω dσ = (4π/3) · id`.

The proof tests the integral against an arbitrary vector `y`: by continuity of
evaluation (`ContinuousLinearMap.integral_apply`) the value at `y` is the vector
integral `∫_{S²} (y - 3 ⟪ω,y⟫ ω) dσ`.  Linearity of the Bochner integral and the
companion result `sphere_integral_inner_smul`,

`∫_{S²} ⟪y,ω⟫ ω dσ = (4π/3) · y`,

reduce this to `(area) · y - 3 · ((4π/3) · y)`, and the area of the unit sphere
`σ(univ) = 4π` (`Measure.toSphere_apply_univ` together with the volume of the
unit ball) makes both terms cancel.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.LWP.Defs
import Submission.Work.CoreResiduals.BiotSavart.KfBall.sphere_integral_inner_smul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory

theorem sphere_integral_kDerivCLM_angular :
    (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
        (ContinuousLinearMap.id ℝ Work.LWP.R3
          - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3))
      ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) = 0 := by
  -- Integrability of the continuous, compactly supported integrand.
  have hcont : Continuous (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
        (ContinuousLinearMap.id ℝ Work.LWP.R3
          - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3))) := by
    fun_prop
  have hint : Integrable (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
        (ContinuousLinearMap.id ℝ Work.LWP.R3
          - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3)))
      ((MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
    exact Integrable.of_bound hcont.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => hC ω (Set.mem_univ ω))
  -- The total mass of the sphere: `σ(univ) = 3 · |B₁| = 3 · (4π/3) = 4π`.
  have hmass : ((MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere).real Set.univ
      = 4 * Real.pi := by
    rw [Measure.toSphere_real_apply_univ]
    have hfr : (Module.finrank ℝ Work.LWP.R3 : ℝ) = 3 := by
      simp [Work.LWP.R3, finrank_euclideanSpace]
    have hball : (MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).real
        (Metric.ball (0 : Work.LWP.R3) 1) = Real.pi * 4 / 3 := by
      rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1),
        ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi * 4 / 3)]
      norm_num
    rw [hfr, hball]; ring
  -- Test the integral against an arbitrary vector `y`.
  apply ContinuousLinearMap.ext
  intro y
  rw [ContinuousLinearMap.integral_apply hint y]
  simp only [zero_apply]
  simp only [sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply]
  have hf1 : Integrable (fun _ : Metric.sphere (0 : Work.LWP.R3) 1 => y)
      ((MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) := integrable_const y
  have hf3 : Integrable (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
      (3 : ℝ) • (inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3)))
      ((MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) := by
    have hc : Continuous (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
        (3 : ℝ) • (inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3))) := by fun_prop
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    exact Integrable.of_bound hc.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => hC ω (Set.mem_univ ω))
  -- The vector second moment of the sphere.
  have hcomp : (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
        inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3)
        ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere)
      = (4 * Real.pi / 3) • y := by
    rw [show (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
          inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3)
          ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere)
        = (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
          inner ℝ y (ω : Work.LWP.R3) • (ω : Work.LWP.R3)
          ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) from
        integral_congr_ae (Filter.Eventually.of_forall fun ω => by
          simp only [real_inner_comm y (ω : Work.LWP.R3)])]
    exact KfBall.sphere_integral_inner_smul y
  -- Linearity of the Bochner integral splits the integrand into the two pieces.
  rw [show (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
        (y - (3 : ℝ) • (inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3)))
        ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere)
      = (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1, y
          ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere)
        - (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
            (3 : ℝ) • (inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3))
          ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) from
      integral_sub hf1 hf3]
  rw [integral_const, integral_smul, hcomp, hmass, ← mul_smul,
    show (3 : ℝ) * (4 * Real.pi / 3) = 4 * Real.pi by ring, sub_self]

end Work.CoreResiduals.BiotSavart
