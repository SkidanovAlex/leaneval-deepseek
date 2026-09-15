import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option linter.style.haveILetI false

namespace Commons.Analysis.Measure

open scoped Real ENNReal BigOperators
open MeasureTheory

/-- Hölder's inequality for countable sums of `ENNReal`s with conjugate exponents `1-κ`, `κ`:
`∑' i, x i^(1-κ) y i^κ ≤ (∑' i, x i)^(1-κ) (∑' i, y i)^κ`. -/
theorem tsum_ennreal_rpow_mul_le {ι : Type*} [Countable ι] (x y : ι → ENNReal)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    ∑' i, (x i) ^ (1 - κ) * (y i) ^ κ ≤ (∑' i, x i) ^ (1 - κ) * (∑' i, y i) ^ κ := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun a => trivial⟩
  have hx : AEMeasurable x MeasureTheory.Measure.count :=
    (measurable_of_countable x).aemeasurable
  have hy : AEMeasurable y MeasureTheory.Measure.count :=
    (measurable_of_countable y).aemeasurable
  have h := ENNReal.lintegral_mul_norm_pow_le hx hy
    (show (0 : ℝ) ≤ 1 - κ by linarith) hκ0.le (show (1 - κ) + κ = 1 by ring)
  calc ∑' i, (x i) ^ (1 - κ) * (y i) ^ κ
      = ∫⁻ i, (x i) ^ (1 - κ) * (y i) ^ κ ∂MeasureTheory.Measure.count :=
        (MeasureTheory.lintegral_count _).symm
    _ ≤ (∫⁻ i, x i ∂MeasureTheory.Measure.count) ^ (1 - κ) *
          (∫⁻ i, y i ∂MeasureTheory.Measure.count) ^ κ := h
    _ = (∑' i, x i) ^ (1 - κ) * (∑' i, y i) ^ κ := by
        rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]

end Commons.Analysis.Measure