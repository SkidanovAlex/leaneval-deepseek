import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.InteriorRegularity.young_l1_l2
import Submission.Work.EllipticEst.InteriorRegularity.Q0.conv_l2_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory

/-- Young's convolution inequality in the form needed for the interior-regularity gain step:
if `f` is dominated pointwise (`‖f x‖ₑ ≤ ∫⁻ y, F (x - y) * u y`) by the convolution of an
integrable nonnegative `F` with a nonnegative `u ∈ L²`, then `‖f‖₂ ≤ ‖F‖₁ ‖u‖₂`.

The analytic content is `conv_l2_lintegral`: the squared `L²` mass of the lintegral
convolution `x ↦ ∫⁻ y, F (x - y) * u y` is bounded by `‖F‖₁² ‖u‖₂²`; the rest is
monotonicity of `eLpNorm` together with the computation of `eLpNorm` as
`(∫⁻ ‖·‖ₑ ^ p) ^ (1/p)`. -/
theorem youngE {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F u : E → ℝ} (hF : ∀ x, 0 ≤ F x) (hu : ∀ x, 0 ≤ u x)
    (hFi : MeasureTheory.Integrable F MeasureTheory.volume)
    (huM : MeasureTheory.MemLp u 2 MeasureTheory.volume)
    {f : E → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hpt : ∀ x : E, ‖f x‖ₑ ≤ ∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) :
    MeasureTheory.eLpNorm f 2 MeasureTheory.volume
      ≤ ENNReal.ofReal (∫ z, F z) * MeasureTheory.eLpNorm u 2 MeasureTheory.volume := by
  -- the analytic core: the `L²` mass of the convolution integrand
  have hcore : (∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ)
        ∂(volume : Measure E))
      ≤ (∫⁻ z, ENNReal.ofReal (F z)) * ((∫⁻ z, ENNReal.ofReal (F z))
          * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := conv_l2_lintegral hF hu hFi huM
  -- `∫⁻ ofReal F = ofReal (∫ F)`
  have hAeq : ENNReal.ofReal (∫ z, F z) = ∫⁻ z, ENNReal.ofReal (F z) :=
    ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF)
  -- `eLpNorm u 2` in lintegral form
  have hunorm : MeasureTheory.eLpNorm u (2:ENNReal) (volume : Measure E)
      = (∫⁻ y, ENNReal.ofReal (u y ^ 2)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_eLpNorm' (p := (2:ENNReal)) (by norm_num) (by norm_num)
        huM.aestronglyMeasurable, eLpNorm'_eq_lintegral_enorm]
    norm_num
    congr 1
    refine lintegral_congr (fun y => ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hu y)]
    exact (ENNReal.ofReal_pow (hu y) 2).symm
  -- `eLpNorm f 2` in lintegral form
  have hfE : MeasureTheory.eLpNorm f (2:ENNReal) (volume : Measure E)
      = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂(volume : Measure E)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ENNReal)) (by norm_num)
      (by norm_num) hf]
    norm_num
  calc MeasureTheory.eLpNorm f (2:ENNReal) (volume : Measure E)
      = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂(volume : Measure E)) ^ ((1:ℝ)/2) := hfE
    _ ≤ (∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ)
          ∂(volume : Measure E)) ^ ((1:ℝ)/2) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono (fun x => ?_)) (by norm_num)
        exact ENNReal.rpow_le_rpow (hpt x) (by norm_num)
    _ ≤ ((∫⁻ z, ENNReal.ofReal (F z)) * ((∫⁻ z, ENNReal.ofReal (F z))
          * ∫⁻ y, ENNReal.ofReal (u y ^ 2))) ^ ((1:ℝ)/2) :=
        ENNReal.rpow_le_rpow hcore (by norm_num)
    _ = ENNReal.ofReal (∫ z, F z) * MeasureTheory.eLpNorm u (2:ENNReal)
          (volume : Measure E) := by
        rw [← mul_assoc, ← pow_two, ← ENNReal.rpow_natCast,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
          ← ENNReal.rpow_mul]
        norm_num
        rw [← hAeq, ← hunorm]

end Work.EllipticEst.InteriorRegularity.Q0
