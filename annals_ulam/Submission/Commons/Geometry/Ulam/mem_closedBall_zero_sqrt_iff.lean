import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Geometry.Ulam

lemma mem_closedBall_zero_sqrt_iff {k : ℕ} {f z : ℝ} {y : EuclideanSpace ℝ (Fin k)}
    (hf : 0 ≤ f) (hz : -f ≤ z ∧ z ≤ f) :
    y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (Real.sqrt (f ^ 2 - z ^ 2)) ↔
      z ^ 2 + ‖y‖ ^ 2 ≤ f ^ 2 := by
  have hz_abs : |z| ≤ f := abs_le.mpr hz
  have hzsq : z ^ 2 ≤ f ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg z) hf).2 hz_abs
  rw [mem_closedBall_zero_iff, Real.le_sqrt (norm_nonneg y) (sub_nonneg.mpr hzsq)]
  constructor <;> intro h <;> nlinarith

end Commons.Geometry.Ulam