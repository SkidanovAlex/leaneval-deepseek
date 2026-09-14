import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.Nat

theorem pow_dvd_le_rpow_mul (n j D M : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D) (hj2 : 2 ≤ j) (hjn : j ≤ n)
    (hdvd : M ^ j ∣ D)
    (hineq : 2 * ((n : ℝ) - 1) ≤ (j : ℝ) * ((n : ℝ) + 1 - (j : ℝ))) :
    (M : ℝ) ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n + 6)) ^ (n + 1 - j) *
      (D : ℝ) ^ (((n + 1 - j : ℕ) : ℝ) / (2 * ((n : ℝ) - 1))) := by
  have hn2 : 2 ≤ n := by omega
  have hn1' : (1 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hjpos : (0 : ℝ) < (j : ℝ) := by
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
    linarith
  have hden : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
  have hk_eq : ((n + 1 - j : ℕ) : ℝ) = (n : ℝ) + 1 - (j : ℝ) := by
    rw [Nat.cast_sub (by omega : j ≤ n + 1)]
    push_cast
    ring
  have hineq' : 2 * ((n : ℝ) - 1) ≤ (j : ℝ) * ((n + 1 - j : ℕ) : ℝ) := by
    rw [hk_eq]; exact hineq
  have hexp : (1 : ℝ) / (j : ℝ) ≤ ((n + 1 - j : ℕ) : ℝ) / (2 * ((n : ℝ) - 1)) := by
    rw [div_le_div_iff₀ hjpos hden]
    nlinarith [hineq']
  have hMj_le : (M : ℝ) ^ (j : ℝ) ≤ (D : ℝ) := by
    have h := Nat.le_of_dvd (by omega : 0 < D) hdvd
    have h2 : (M : ℝ) ^ j ≤ (D : ℝ) := by exact_mod_cast h
    rwa [Real.rpow_natCast]
  have hMeq : (M : ℝ) = ((M : ℝ) ^ (j : ℝ)) ^ ((1 : ℝ) / (j : ℝ)) := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ (M : ℝ) by positivity)]
    rw [show (j : ℝ) * ((1 : ℝ) / (j : ℝ)) = 1 by
      rw [mul_one_div, div_self hjpos.ne']]
    rw [Real.rpow_one]
  have hM_le : (M : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := by
    rw [hMeq]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hMj_le (by positivity)
  have hD_rpow : (D : ℝ) ^ ((1 : ℝ) / (j : ℝ)) ≤
      (D : ℝ) ^ (((n + 1 - j : ℕ) : ℝ) / (2 * ((n : ℝ) - 1))) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hD) hexp
  have hfac : (1 : ℝ) ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n + 6)) ^ (n + 1 - j) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num))
      (one_le_pow₀ (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)))
  calc (M : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := hM_le
    _ ≤ (D : ℝ) ^ (((n + 1 - j : ℕ) : ℝ) / (2 * ((n : ℝ) - 1))) := hD_rpow
    _ ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n + 6)) ^ (n + 1 - j) *
          (D : ℝ) ^ (((n + 1 - j : ℕ) : ℝ) / (2 * ((n : ℝ) - 1))) := by
        have hDnn : (0 : ℝ) ≤ (D : ℝ) ^ (((n + 1 - j : ℕ) : ℝ) / (2 * ((n : ℝ) - 1))) :=
          Real.rpow_nonneg (by positivity) _
        have h := mul_le_mul_of_nonneg_right hfac hDnn
        simpa using h

end Commons.NumberTheory.Nat