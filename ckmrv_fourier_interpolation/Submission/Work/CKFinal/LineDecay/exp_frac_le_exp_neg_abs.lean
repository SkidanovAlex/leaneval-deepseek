import Mathlib

namespace Work.CKFinal.LineDecay

open Real

/-- Multiplication of numerator and denominator by `exp (2*a)`:
`exp (-a) / (1 + exp (-2a)) = exp a / (1 + exp (2a))`. -/
lemma exp_neg_div_one_add_exp (a : ℝ) :
    Real.exp (-a) / (1 + Real.exp (-(2 * a))) = Real.exp a / (1 + Real.exp (2 * a)) := by
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have h1 : Real.exp (-a) * Real.exp (2 * a) = Real.exp a := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp a * Real.exp (-(2 * a)) = Real.exp (-a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [mul_add, mul_one, h1, mul_add, mul_one, h2]
  ring

/-- The core inequality: `exp a / (1 + exp (2a)) ≤ exp (-|a|)`. -/
lemma exp_div_one_add_exp_two_mul_le (a : ℝ) :
    Real.exp a / (1 + Real.exp (2 * a)) ≤ Real.exp (-(|a|)) := by
  rw [div_le_iff₀ (by positivity)]
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    have h1 : Real.exp (-a) * Real.exp (2 * a) = Real.exp a := by
      rw [← Real.exp_add]; congr 1; ring
    rw [mul_add, mul_one, h1]
    exact le_add_of_nonneg_left (Real.exp_pos (-a)).le
  · rw [abs_of_neg (lt_of_not_ge ha)]
    rw [neg_neg, mul_add, mul_one]
    exact le_add_of_nonneg_right (by positivity)

lemma exp_frac_le_exp_neg_abs (y t : ℝ) :
    Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))) ≤ Real.exp (-(Real.pi * |t - y|)) * Real.exp (-(Real.pi * y)) := by
  have hnum : Real.exp (-(Real.pi * t))
      = Real.exp (-(Real.pi * y)) * Real.exp (-(Real.pi * (t - y))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hden : 2 * Real.pi * (y - t) = -(2 * (Real.pi * (t - y))) := by ring
  rw [hnum, hden, mul_div_assoc, exp_neg_div_one_add_exp]
  have hcore := exp_div_one_add_exp_two_mul_le (Real.pi * (t - y))
  have habs : |Real.pi * (t - y)| = Real.pi * |t - y| := by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
  calc Real.exp (-(Real.pi * y))
          * (Real.exp (Real.pi * (t - y)) / (1 + Real.exp (2 * (Real.pi * (t - y)))))
      ≤ Real.exp (-(Real.pi * y)) * Real.exp (-(|Real.pi * (t - y)|)) :=
        mul_le_mul_of_nonneg_left hcore (Real.exp_pos _).le
    _ = Real.exp (-(Real.pi * |t - y|)) * Real.exp (-(Real.pi * y)) := by
        rw [habs]; ring

end Work.CKFinal.LineDecay
