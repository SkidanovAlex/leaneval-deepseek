import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Real

lemma cos_pi_mul_lower_bound_on_quarter (t : ℝ) (ht : |t| ≤ 1 / 4) :
    Real.sqrt 2 / 2 ≤ Real.cos (Real.pi * t) := by
  have hle : |Real.pi * t| ≤ Real.pi / 4 := by
    calc
      |Real.pi * t| = Real.pi * |t| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ Real.pi * (1 / 4) := by
        exact mul_le_mul_of_nonneg_left ht (le_of_lt Real.pi_pos)
      _ = Real.pi / 4 := by ring
  have hc : Real.cos (Real.pi / 4) ≤ Real.cos (Real.pi * t) := by
    have h' : Real.cos (Real.pi / 4) ≤ Real.cos (|Real.pi * t|) := by
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (Real.pi * t))
        (by linarith [Real.pi_pos]) hle
    rw [Real.cos_abs] at h'
    exact h'
  calc
    Real.sqrt 2 / 2 = Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]
    _ ≤ Real.cos (Real.pi * t) := hc

end Commons.Analysis.Real