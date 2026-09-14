import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.Analysis.Integral

theorem measurable_phiFun_kernel :
    Measurable (fun v : ℝ => (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1)) := by
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  simp only [intervalIntegral.integral_of_le hπ]
  have hsm : MeasureTheory.StronglyMeasurable (fun v : ℝ =>
      ∫ theta, (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1)
        ∂(MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi)))) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right
      (ν := MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi)))
      (f := fun v theta => (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1))
      (by measurability)
  exact measurable_const.mul hsm.measurable

end Commons.Analysis.Integral