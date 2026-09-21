import Mathlib

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false

lemma abs_t_add_r_line_le_general {t r T R H : ℝ} {h : ℝ → ℝ}
    (ht : |t| ≤ T) (hr : |r| ≤ R) (hL : |r * t + h r| ≤ R * T + H) :
    |t + r * (r * t + h r)| ≤ T + R * (R * T + H) := by
  have hRnonneg : 0 ≤ R := le_trans (abs_nonneg r) hr
  calc
    |t + r * (r * t + h r)| ≤ |t| + |r * (r * t + h r)| := abs_add_le _ _
    _ = |t| + |r| * |r * t + h r| := by rw [abs_mul]
    _ ≤ T + R * (R * T + H) := by
      exact add_le_add ht (mul_le_mul hr hL (abs_nonneg _) hRnonneg)

lemma abs_t_add_deriv_le_general {t T C : ℝ} {h : ℝ → ℝ} {r : ℝ}
    (ht : |t| ≤ T) (hd : |deriv h r| ≤ C) :
    |t + deriv h r| ≤ T + C := by
  calc
    |t + deriv h r| ≤ |t| + |deriv h r| := abs_add_le _ _
    _ ≤ T + C := add_le_add ht hd

end Commons.Geometry.Ulam
