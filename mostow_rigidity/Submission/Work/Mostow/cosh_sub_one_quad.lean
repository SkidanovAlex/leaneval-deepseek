import Mathlib
import Submission.Work.Mostow.sinh_le_mul_cosh

open Set

namespace Work.Mostow

theorem cosh_sub_one_quad (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    2 * (Real.cosh t - 1) ≤ Real.cosh 1 ^ 2 * t ^ 2 := by
  have hkey : 2 * (Real.cosh t - 1) = 4 * Real.sinh (t / 2) ^ 2 := by
    have hct : Real.cosh t = Real.cosh (t / 2) ^ 2 + Real.sinh (t / 2) ^ 2 := by
      have h := Real.cosh_two_mul (t / 2)
      rwa [show (2 : ℝ) * (t / 2) = t by ring] at h
    have hcs : Real.cosh (t / 2) ^ 2 = Real.sinh (t / 2) ^ 2 + 1 := Real.cosh_sq (t / 2)
    rw [hct, hcs]
    ring
  have ht2 : 0 ≤ t / 2 := by linarith
  have hsin : Real.sinh (t / 2) ≤ (t / 2) * Real.cosh 1 := by
    have h1' := sinh_le_mul_cosh (t / 2) ht2
    have hc : Real.cosh (t / 2) ≤ Real.cosh 1 := by
      rw [Real.cosh_le_cosh, abs_of_nonneg ht2, abs_one]
      linarith
    have h2' := mul_le_mul_of_nonneg_left hc ht2
    linarith
  have hsinnn : 0 ≤ Real.sinh (t / 2) := Real.sinh_nonneg_iff.mpr ht2
  have hsq : Real.sinh (t / 2) ^ 2 ≤ ((t / 2) * Real.cosh 1) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hsinnn, abs_of_nonneg (mul_nonneg ht2 (Real.cosh_pos 1).le)]
    exact hsin
  calc 2 * (Real.cosh t - 1) = 4 * Real.sinh (t / 2) ^ 2 := hkey
    _ ≤ 4 * ((t / 2) * Real.cosh 1) ^ 2 := by linarith
    _ = Real.cosh 1 ^ 2 * t ^ 2 := by ring

end Work.Mostow
