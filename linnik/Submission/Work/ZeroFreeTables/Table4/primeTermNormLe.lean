import Mathlib

/-!
# ZeroFreeTables/Table4/primeTermNormLe

`‖log p / (p^z - 1)‖ ≤ 2 log p / p` for a prime `p` and `Re z ≥ 1` — the pointwise
Euler-factor bound behind HB Table 4 (used by `eulerFactorBound`).
-/

namespace Work.ZeroFreeTables.Table4

theorem primeTermNormLe (p : ℕ) (hp : p.Prime) (z : ℂ) (hz : 1 ≤ z.re) :
    ‖(Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)‖ ≤ 2 * Real.log (p : ℝ) / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hnorm : ‖(p : ℂ) ^ z‖ = (p : ℝ) ^ z.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hppos z
  have hge : (p : ℝ) ≤ ‖(p : ℂ) ^ z‖ := by
    rw [hnorm]
    calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (p : ℝ) ^ z.re := Real.rpow_le_rpow_of_exponent_le (by linarith) hz
  have hden : (p : ℝ) / 2 ≤ ‖(p : ℂ) ^ z - 1‖ := by
    have h1 : ‖(p : ℂ) ^ z‖ - ‖(1 : ℂ)‖ ≤ ‖(p : ℂ) ^ z - 1‖ := norm_sub_norm_le _ _
    rw [norm_one] at h1
    linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  calc Real.log (p : ℝ) / ‖(p : ℂ) ^ z - 1‖
      ≤ Real.log (p : ℝ) / ((p : ℝ) / 2) :=
        div_le_div_of_nonneg_left hlog (by linarith) hden
    _ = 2 * Real.log (p : ℝ) / (p : ℝ) := by
        rw [div_div_eq_mul_div]
        ring

end Work.ZeroFreeTables.Table4
