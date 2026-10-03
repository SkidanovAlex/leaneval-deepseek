import Mathlib

namespace Work.Pert.Count

theorem count_arith_small {a s : ℝ} {n : ℕ} (ha : 0 < a) (hs : a ≤ s) (hs2 : 2 * s ≤ 1) :
    (((33 : ℝ) / 32) * (n : ℝ) * a + 2 * s + 1) * (6 * (s / a) + 1)
      ≤ 30 * (s / a) * (1 + (n : ℝ) * a) := by
  have hne : a ≠ 0 := ne_of_gt ha
  -- Clear the denominator `a` (which is positive): it suffices to prove
  -- `A * (6*s + a) ≤ 30*s*(1 + n*a)` with `A = (33/32)*n*a + 2*s + 1`.
  have key : (((33 : ℝ) / 32) * (n : ℝ) * a + 2 * s + 1) * (6 * s + a)
      ≤ 30 * s * (1 + (n : ℝ) * a) := by
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hs0 : (0:ℝ) ≤ s := le_trans ha.le hs
    have hna : (0:ℝ) ≤ (n:ℝ)*a := mul_nonneg hn ha.le
    -- `762*s - 33*a ≥ 0` since `s ≥ a > 0`: the `n*a*s` coefficient is positive,
    have h1 : (0:ℝ) ≤ 762*s - 33*a := by linarith
    have hn1 : (0:ℝ) ≤ (n:ℝ)*a*(762*s-33*a) := mul_nonneg hna h1
    -- and the constant coefficient `s*(23 - 14*s) ≥ 0` since `s ≤ 1/2`.
    have h2 : (0:ℝ) ≤ 23 - 14*s := by linarith
    have hs2' : (0:ℝ) ≤ s*(23-14*s) := mul_nonneg hs0 h2
    nlinarith [hn1, hs2']
  calc
    (((33 : ℝ) / 32) * (n : ℝ) * a + 2 * s + 1) * (6 * (s / a) + 1)
        = ((((33 : ℝ) / 32) * (n : ℝ) * a + 2 * s + 1) * (6 * s + a)) / a := by
          field_simp
    _ ≤ (30 * s * (1 + (n : ℝ) * a)) / a := div_le_div_of_nonneg_right key ha.le
    _ = 30 * (s / a) * (1 + (n : ℝ) * a) := by field_simp

end Work.Pert.Count
