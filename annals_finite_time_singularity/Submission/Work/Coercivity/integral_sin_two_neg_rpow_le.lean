import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.integral_majorant_rpow
import Submission.Work.Spaces.integrableOn_majorant_rpow
import Submission.Work.Spaces.sin_rpow_le_majorant_pi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The angular integral of `sin(2θ)^{-q}` over `Iθ = [0,π/2]` is finite and bounded by
`4/(1-q)` for `0 < q < 1`.

The integrand has integrable singularities at both endpoints `θ = 0` and `θ = π/2`.
Jordan's inequality `sin(2θ) ≥ (4/π)θ` gives the pointwise majorant
`sin(2θ)^{-q} ≤ (π/4)^q (θ^{-q} + (π/2-θ)^{-q})` on `Iθ`, which is integrable with
integral `π (1/2)^q / (1-q) ≤ 4/(1-q)`. -/
theorem integral_sin_two_neg_rpow_le (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) ≤ 4 / (1 - q) := by
  have hden : (0 : ℝ) < 1 - q := by linarith
  -- The majorant, its integrability, and its integral.
  have hGint : Integrable
      (fun θ : ℝ => (Real.pi / 4) ^ q * (θ ^ (-q) + (Real.pi / 2 - θ) ^ (-q)))
      (volume.restrict Work.Spaces.Iθ) := by
    rw [Work.Spaces.Iθ]
    exact Work.Spaces.integrableOn_majorant_rpow q hq0 hq1
  have hGval : ∫ θ in Work.Spaces.Iθ,
        ((Real.pi / 4) ^ q * (θ ^ (-q) + (Real.pi / 2 - θ) ^ (-q)))
      = Real.pi * (1 / 2) ^ q / (1 - q) := by
    rw [Work.Spaces.Iθ]
    exact Work.Spaces.integral_majorant_rpow q hq0 hq1
  -- Nonnegativity of the integrand on `Iθ`.
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Real.rpow_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) (-q)
  -- The pointwise majorant.
  have hpoint : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.pi / 4) ^ q * (θ ^ (-q) + (Real.pi / 2 - θ) ^ (-q))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Work.Spaces.sin_rpow_le_majorant_pi q θ hq0 hθ
  -- Measurability of the integrand.
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q))
      (volume.restrict Work.Spaces.Iθ) :=
    (Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) (-q))
      |>.aestronglyMeasurable
  -- Domination of the norms.
  have hnorm : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖(Real.sin (2 * θ)) ^ (-q)‖
        ≤ (Real.pi / 4) ^ q * (θ ^ (-q) + (Real.pi / 2 - θ) ^ (-q)) := by
    filter_upwards [hpoint, hnonneg] with θ h1 h2
    rw [Real.norm_of_nonneg h2]
    exact h1
  constructor
  · exact hGint.mono' hmeas hnorm
  · calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        ≤ ∫ θ in Work.Spaces.Iθ,
            ((Real.pi / 4) ^ q * (θ ^ (-q) + (Real.pi / 2 - θ) ^ (-q))) :=
          integral_mono_of_nonneg hnonneg hGint hpoint
      _ = Real.pi * (1 / 2) ^ q / (1 - q) := hGval
      _ ≤ 4 / (1 - q) := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hden)
          have hhalf : (1 / 2 : ℝ) ^ q ≤ 1 :=
            Real.rpow_le_one (by norm_num) (by norm_num) (le_of_lt hq0)
          have hnum : Real.pi * (1 / 2) ^ q ≤ 4 := by
            calc Real.pi * (1 / 2) ^ q ≤ 4 * 1 :=
                  mul_le_mul (le_of_lt Real.pi_lt_four) hhalf (by positivity) (by norm_num)
              _ = 4 := by norm_num
          linarith

end Work.Coercivity
