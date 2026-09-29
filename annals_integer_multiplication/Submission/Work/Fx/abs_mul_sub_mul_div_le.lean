import Mathlib

namespace Work.Fx

theorem abs_mul_sub_mul_div_le {k : ℕ} (hk : 1 ≤ k) {r : ℤ} (hr0 : 0 ≤ r) (hrk : r < k)
    {u : ℤ} {M : ℝ} (hu : |(u : ℝ) - M| ≤ 1) :
    |(2 * (u : ℝ) * (r : ℝ)) / (k : ℝ) - (2 * (r : ℝ) / (k : ℝ)) * M| ≤ 2 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by positivity
  have hrkR : (r : ℝ) < (k : ℝ) := by exact_mod_cast hrk
  set c : ℝ := 2 * (r : ℝ) / (k : ℝ) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]; positivity
  have hkey : (2 * (u : ℝ) * (r : ℝ)) / (k : ℝ) - (2 * (r : ℝ) / (k : ℝ)) * M
      = c * ((u : ℝ) - M) := by
    rw [hc]; ring
  rw [hkey, abs_mul, abs_of_nonneg hc0]
  have hc2 : c ≤ 2 := by
    rw [hc, div_le_iff₀ hkR]
    nlinarith [hrkR]
  calc c * |(u : ℝ) - M| ≤ c * 1 := mul_le_mul_of_nonneg_left hu hc0
    _ = c := mul_one c
    _ ≤ 2 := hc2

end Work.Fx
