import Mathlib

namespace Work.BG

/-- Pure-rational core inequality: for a rational `x` with `9 ≤ |x|`,
`(1 - 3/|x|) * x * (x+1)` is strictly below `(x-1)^2`.

This is the arithmetic heart: after multiplying the target by the positive
quantity `x * (x+1)` it reduces to comparing `(x ± 3)(x+1)` with `(x-1)^2`. -/
theorem key_ineq (x : ℚ) (hx : 9 ≤ |x|) :
    (1 - 3 / |x|) * (x * (x + 1)) < (x - 1) ^ 2 := by
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at hx ⊢
    have hc : (1 - 3 / x) * (x * (x + 1)) = (x - 3) * (x + 1) := by
      field_simp
    rw [hc]; nlinarith
  · rw [abs_of_neg hx0] at hx ⊢
    have hxne : x ≠ 0 := ne_of_lt hx0
    have hc : (1 - 3 / -x) * (x * (x + 1)) = (x + 3) * (x + 1) := by
      field_simp [hxne]; ring
    rw [hc]; nlinarith

theorem thmCBigIneqArith (N k : ℕ) (d : ℤ) (hN : 0 < N)
    (h9 : 9 ≤ |d|)
    (hKey : (N : ℤ) * (d - 1) ^ 2 = 2 * (k : ℤ) ^ 2 * d * (d + 1)) :
    (N : ℚ) * (1 - 3 / |(d : ℚ)|) < 2 * (k : ℚ) ^ 2 := by
  have hx9 : (9 : ℚ) ≤ |(d : ℚ)| := by
    rw [← Int.cast_abs]; exact_mod_cast h9
  have hkey := key_ineq (d : ℚ) hx9
  have hNq : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hq : (N : ℚ) * ((d : ℚ) - 1) ^ 2
      = 2 * (k : ℚ) ^ 2 * (d : ℚ) * ((d : ℚ) + 1) := by
    exact_mod_cast hKey
  have hcpos : 0 < (d : ℚ) * ((d : ℚ) + 1) := by
    rcases le_or_gt 0 (d : ℚ) with h | h
    · have h9d : (9 : ℚ) ≤ (d : ℚ) := by rwa [abs_of_nonneg h] at hx9
      exact mul_pos (by linarith) (by linarith)
    · have h9d : (d : ℚ) ≤ -9 := by rw [abs_of_neg h] at hx9; linarith
      exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have step : (N : ℚ) * ((1 - 3 / |(d : ℚ)|) * ((d : ℚ) * ((d : ℚ) + 1)))
      < (2 * (k : ℚ) ^ 2) * ((d : ℚ) * ((d : ℚ) + 1)) := by
    have hs := mul_lt_mul_of_pos_left hkey hNq
    rw [hq] at hs
    ring_nf at hs ⊢
    exact hs
  have hstep : (N : ℚ) * (1 - 3 / |(d : ℚ)|) * ((d : ℚ) * ((d : ℚ) + 1))
      < (2 * (k : ℚ) ^ 2) * ((d : ℚ) * ((d : ℚ) + 1)) := by
    rw [mul_assoc]; exact step
  exact lt_of_mul_lt_mul_right hstep (le_of_lt hcpos)

end Work.BG
