import Mathlib

namespace Work.EQ

/-- One-sided (sharp) form of the triangle inequality for the Euclidean norm on `ℝ²`:
`√(a²+b²) ≤ √(c²+d²) + |a-c| + |b-d|`. -/
lemma sqrt_add_sq_le_sqrt_add_sq_add_abs (a b c d : ℝ) :
    Real.sqrt (a^2 + b^2) ≤ Real.sqrt (c^2 + d^2) + (|a - c| + |b - d|) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hc : |c| ≤ Real.sqrt (c^2+d^2) := by
      rw [Real.le_sqrt (abs_nonneg c) (by positivity)]
      nlinarith [sq_abs c, sq_nonneg d]
    have hd : |d| ≤ Real.sqrt (c^2+d^2) := by
      rw [Real.le_sqrt (abs_nonneg d) (by positivity)]
      nlinarith [sq_abs d, sq_nonneg c]
    have e1 : c * (a-c) ≤ Real.sqrt (c^2+d^2) * |a - c| := by
      calc c * (a-c) ≤ |c * (a-c)| := le_abs_self _
        _ = |c| * |a - c| := by rw [abs_mul]
        _ ≤ Real.sqrt (c^2+d^2) * |a - c| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    have e2 : d * (b-d) ≤ Real.sqrt (c^2+d^2) * |b - d| := by
      calc d * (b-d) ≤ |d * (b-d)| := le_abs_self _
        _ = |d| * |b - d| := by rw [abs_mul]
        _ ≤ Real.sqrt (c^2+d^2) * |b - d| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
    have e3 : (a-c)^2 + (b-d)^2 ≤ (|a-c| + |b-d|)^2 := by
      nlinarith [sq_abs (a-c), sq_abs (b-d), abs_nonneg (a-c), abs_nonneg (b-d)]
    have hB2 : (Real.sqrt (c^2+d^2))^2 = c^2+d^2 := Real.sq_sqrt (by positivity)
    nlinarith [e1, e2, e3, hB2]

theorem lmSqrtLipschitz (u v u' v' : ℝ) :
    |Real.sqrt (u^2 + v^2) - Real.sqrt (u'^2 + v'^2)| ≤ |u - u'| + |v - v'| := by
  have h1 := sqrt_add_sq_le_sqrt_add_sq_add_abs u v u' v'
  have h2 := sqrt_add_sq_le_sqrt_add_sq_add_abs u' v' u v
  rw [abs_sub_comm u' u, abs_sub_comm v' v] at h2
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

end Work.EQ
