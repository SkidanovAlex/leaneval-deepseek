import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped MeasureTheory

namespace Commons.Analysis.Integral

theorem integral_comp_linearMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    {A : E →ₗ[ℝ] E} (hA : LinearMap.det A ≠ 0) {F : E → ℝ}
    (hF : MeasureTheory.Integrable F μ) :
    ∫ x, F (A x) ∂μ = |(LinearMap.det A)⁻¹| * ∫ y, F y ∂μ := by
  have hA_meas : AEMeasurable A μ := A.continuous_of_finiteDimensional.aemeasurable
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar μ hA
  have hle : MeasureTheory.Measure.map A μ ≪ μ := by
    rw [hmap]; exact MeasureTheory.Measure.smul_absolutelyContinuous
  have hF' : AEStronglyMeasurable F (MeasureTheory.Measure.map A μ) :=
    AEStronglyMeasurable.mono_ac hle hF.aestronglyMeasurable
  rw [← MeasureTheory.integral_map hA_meas hF']
  rw [hmap, MeasureTheory.integral_smul_measure]
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

end Commons.Analysis.Integral