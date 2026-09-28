import Mathlib

namespace Work.HP.NA

theorem rpow_half_div_pow_le (p : ℝ) (hp : 2 ≤ p) (n : ℕ) (hn : 3 ≤ n) :
    p ^ ((1:ℝ)/2) / p ^ (n - 1) ≤ 1 / p ^ ((5:ℝ)/4) := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1:ℝ) ≤ p := by linarith
  rw [← Real.rpow_natCast p (n - 1)]
  rw [← Real.rpow_sub hp0 (1/2) (((n - 1 : ℕ) : ℝ))]
  rw [show (1:ℝ) / p ^ ((5:ℝ)/4) = p ^ (-((5:ℝ)/4)) by
        rw [Real.rpow_neg hp0.le, one_div]]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  rw [hn1]
  linarith

end Work.HP.NA
