import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.Nat

theorem sq_dvd_le_rpow_mul (n D M : ℕ) (hn : 2 ≤ n) (hD : 1 ≤ D) (hdvd : M ^ 2 ∣ D) :
    (M : ℝ) ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n + 6)) ^ n *
      (D : ℝ) ^ ((n : ℝ) / (2 * ((n : ℝ) - 1))) := by
  have hDpos : 0 < D := by omega
  -- M^2 ≤ D as naturals
  have hM2le : M ^ 2 ≤ D := Nat.le_of_dvd hDpos hdvd
  have hcast : (M : ℝ) ^ 2 ≤ (D : ℝ) := by exact_mod_cast hM2le
  -- M ≤ sqrt D
  have hMsqrt : (M : ℝ) ≤ Real.sqrt (D : ℝ) := by
    have h := Real.sqrt_le_sqrt hcast
    rwa [Real.sqrt_sq (Nat.cast_nonneg M)] at h
  rw [Real.sqrt_eq_rpow] at hMsqrt
  -- exponent relation: 1/2 ≤ n / (2(n-1))
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have he : (1 : ℝ) / 2 ≤ (n : ℝ) / (2 * ((n : ℝ) - 1)) := by
    have hpos : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hpos]
    linarith
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hrpow : (D : ℝ) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) ^ ((n : ℝ) / (2 * ((n : ℝ) - 1))) :=
    Real.rpow_le_rpow_of_exponent_le hD1 he
  have hMle : (M : ℝ) ≤ (D : ℝ) ^ ((n : ℝ) / (2 * ((n : ℝ) - 1))) := hMsqrt.trans hrpow
  -- constant factor is at least one
  have hC : (1 : ℝ) ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n + 6)) ^ n :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (one_le_pow₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have hDe : 0 ≤ (D : ℝ) ^ ((n : ℝ) / (2 * ((n : ℝ) - 1))) :=
    Real.rpow_nonneg (Nat.cast_nonneg D) _
  calc (M : ℝ) ≤ (D : ℝ) ^ ((n : ℝ) / (2 * ((n : ℝ) - 1))) := hMle
    _ = 1 * (D : ℝ) ^ ((n : ℝ) / (2 * ((n : ℝ) - 1))) := (one_mul _).symm
    _ ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n + 6)) ^ n *
          (D : ℝ) ^ ((n : ℝ) / (2 * ((n : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_right hC hDe

end Commons.NumberTheory.Nat