import Mathlib

namespace Work.FIArea4.Vflip.Vfd

theorem rpow_dyadic_ident (d H x : ℝ) (hd : 0 < d) (hH : 0 < H) (hx : x = d * H ^ 3) :
    (d * H * x) ^ ((1 : ℝ) / 2) = d ^ ((1 : ℝ) / 3) * x ^ ((2 : ℝ) / 3) := by
  subst hx
  have hd0 : (0 : ℝ) ≤ d := le_of_lt hd
  have hH0 : (0 : ℝ) ≤ H := le_of_lt hH
  have hL : (d * H * (d * H ^ 3)) ^ ((1 : ℝ) / 2) = d * H ^ 2 := by
    have hy : (0 : ℝ) ≤ d * H ^ 2 := by positivity
    rw [show d * H * (d * H ^ 3) = (d * H ^ 2) ^ 2 by ring]
    rw [← Real.sqrt_eq_rpow ((d * H ^ 2) ^ 2), Real.sqrt_sq hy]
  have hR : d ^ ((1 : ℝ) / 3) * (d * H ^ 3) ^ ((2 : ℝ) / 3) = d * H ^ 2 := by
    have hH30 : (0 : ℝ) ≤ H ^ 3 := by positivity
    rw [Real.mul_rpow hd0 hH30]
    have hH3 : (H ^ 3) ^ ((2 : ℝ) / 3) = H ^ 2 := by
      rw [show (H ^ 3 : ℝ) = H ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast H 3).symm]
      rw [show H ^ ((3 : ℕ) : ℝ) = H ^ (3 : ℝ) from rfl]
      rw [← Real.rpow_mul hH0 (3 : ℝ) ((2 : ℝ) / 3)]
      rw [show (3 : ℝ) * ((2 : ℝ) / 3) = (2 : ℝ) by norm_num]
      exact Real.rpow_natCast H 2
    rw [hH3, ← mul_assoc, ← Real.rpow_add hd ((1 : ℝ) / 3) ((2 : ℝ) / 3)]
    rw [show (1 : ℝ) / 3 + (2 : ℝ) / 3 = 1 by norm_num, Real.rpow_one]
  rw [hL, hR]

end Work.FIArea4.Vflip.Vfd
