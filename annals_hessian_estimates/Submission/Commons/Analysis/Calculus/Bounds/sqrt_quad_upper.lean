import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Calculus.Bounds

theorem sqrt_quad_upper {a b P Q : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : a * P ^ 2 - 2 * b * P ≤ Q) :
    P ≤ (b + Real.sqrt (b ^ 2 + a * Q)) / a := by
  have hR : 0 ≤ b ^ 2 + a * Q := by nlinarith [sq_nonneg b, mul_nonneg ha.le hQ]
  have hsq : (a * P - b) ^ 2 ≤ b ^ 2 + a * Q := by nlinarith [h, ha]
  have habs : |a * P - b| ≤ Real.sqrt (b ^ 2 + a * Q) := by
    have h1 : Real.sqrt ((a * P - b) ^ 2) ≤ Real.sqrt (b ^ 2 + a * Q) := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs] at h1
  have hle : a * P - b ≤ Real.sqrt (b ^ 2 + a * Q) := le_trans (le_abs_self _) habs
  rw [le_div_iff₀ ha]
  linarith

end Commons.Analysis.Calculus.Bounds