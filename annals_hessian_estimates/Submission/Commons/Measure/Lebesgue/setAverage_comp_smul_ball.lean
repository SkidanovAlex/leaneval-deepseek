import Mathlib

namespace Commons.Measure.Lebesgue

open scoped Pointwise

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem setAverage_comp_smul_ball {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {r t : ℝ}
    (ht : 0 < t) (hr : 0 < r) :
    (⨍ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, f (t • y))
      = ⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (t * r), f z := by
  rw [setAverage_eq, setAverage_eq]
  rw [Measure.setIntegral_comp_smul_of_pos volume f
    (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) ht]
  have hsb : t • Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
      = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (t * r) := by
    rw [smul_ball ht.ne' 0 r, smul_zero, Real.norm_eq_abs, abs_of_pos ht]
  rw [hsb]
  have hreal : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (t * r))
      = t ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) *
        volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
    rw [Measure.real_def, Measure.real_def, ← hsb]
    rw [Measure.addHaar_smul, abs_of_nonneg (pow_nonneg ht.le _)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht.le _)]
  rw [smul_smul, hreal, mul_inv_rev]

end Commons.Measure.Lebesgue
