import Mathlib

namespace Work.EKLComp

/-- Auxiliary bound: for every real `t`, `exp(-t) * t` is at most `i * exp(-t) + (i+1) * exp(-i)`.
The point is that `s ↦ s * exp(-s)` is maximized at `s = 1`, so `(t - i) * exp(-t) ≤ exp(-(i+1))`,
and `exp(-(i+1)) ≤ (i+1) * exp(-i)`. -/
private theorem exp_neg_mul_le_index (t : ℝ) (i : ℕ) :
    Real.exp (-t) * t ≤
      (i : ℝ) * Real.exp (-t) + (i : ℝ) * Real.exp (-(i : ℝ)) + Real.exp (-(i : ℝ)) := by
  have hmain : (t - (i : ℝ)) * Real.exp (-t) ≤ ((i : ℝ) + 1) * Real.exp (-(i : ℝ)) := by
    have h := Real.mul_exp_neg_le_exp_neg_one (t - (i : ℝ))
    have harg : -(t - (i : ℝ)) + -(i : ℝ) = -t := by ring
    have he : ((t - (i : ℝ)) * Real.exp (-(t - (i : ℝ)))) * Real.exp (-(i : ℝ))
        = (t - (i : ℝ)) * Real.exp (-t) := by
      rw [mul_assoc, ← Real.exp_add, harg]
    calc (t - (i : ℝ)) * Real.exp (-t)
        = ((t - (i : ℝ)) * Real.exp (-(t - (i : ℝ)))) * Real.exp (-(i : ℝ)) := he.symm
      _ ≤ Real.exp (-1) * Real.exp (-(i : ℝ)) := by
            exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ ≤ ((i : ℝ) + 1) * Real.exp (-(i : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            have h1 : Real.exp (-1) ≤ 1 := by
              rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
            have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
            linarith
  calc Real.exp (-t) * t
      = (i : ℝ) * Real.exp (-t) + (t - (i : ℝ)) * Real.exp (-t) := by ring
    _ ≤ (i : ℝ) * Real.exp (-t) + (((i : ℝ) + 1) * Real.exp (-(i : ℝ))) := by linarith
    _ = (i : ℝ) * Real.exp (-t) + (i : ℝ) * Real.exp (-(i : ℝ)) + Real.exp (-(i : ℝ)) := by ring

theorem mul_log_inv_le_index (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (i : ℕ) :
    x * Real.log (1 / x) ≤ (i : ℝ) * x + (i : ℝ) * Real.exp (-(i : ℝ)) + Real.exp (-(i : ℝ)) := by
  rcases hx0.eq_or_lt with h0 | hx
  · subst h0
    simp only [one_div, mul_zero, zero_mul, zero_add]
    positivity
  · set t := Real.log (1 / x) with ht
    have hxt : x = Real.exp (-t) := by
      rw [ht, one_div, Real.log_inv, neg_neg, Real.exp_log hx]
    rw [hxt]
    exact exp_neg_mul_le_index t i

end Work.EKLComp
