import Mathlib

namespace Work.KMTPlan.A6

/-- **The threshold beyond which the exponential `2^{ρL}` dominates the linear `L`.**

If `L ≥ ⌈16/ρ²⌉` then `ρ²L ≥ 16`, hence `ρL ≥ 4√L`; on the other hand `log L ≤ 2√L`
(`Real.log_le_rpow_div` with `ε = 1/2`), so `log L ≤ (ρL)·log 2` because `log 2 ≥ 1/2`.
`Real.le_rpow_iff_log_le` turns this back into `L ≤ 2^{ρL}`. -/
theorem le_two_rpow_self_of_ceil (ρ : ℝ) (hρ : 0 < ρ) (L : ℕ)
    (hL : Nat.ceil (16 / ρ ^ 2) ≤ L) : (L : ℝ) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
  have h16ρ : (16 : ℝ) / ρ ^ 2 ≤ (L : ℝ) := Nat.ceil_le.mp hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le (by positivity) h16ρ
  -- `16 ≤ ρ²L`
  have h16 : (16 : ℝ) ≤ ρ ^ 2 * (L : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ρ ^ 2)] at h16ρ
    linarith
  -- `4√L ≤ ρL`
  have h4s : 4 * Real.sqrt (L : ℝ) ≤ ρ * (L : ℝ) := by
    have hsq : (L : ℝ) ≤ (ρ * (L : ℝ) / 4) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right h16 (le_of_lt hLpos)
      nlinarith [h]
    have hle : Real.sqrt (L : ℝ) ≤ ρ * (L : ℝ) / 4 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
    linarith
  -- `log L ≤ 2√L`
  have hlogL : Real.log (L : ℝ) ≤ 2 * Real.sqrt (L : ℝ) := by
    have h := Real.log_le_rpow_div (x := (L : ℝ)) (le_of_lt hLpos) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    have h2 : Real.sqrt (L : ℝ) / (1 / 2) = 2 * Real.sqrt (L : ℝ) := by ring
    linarith
  -- `log 2 ≥ 1/2`
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [Real.le_rpow_iff_log_le hLpos (by norm_num : (0 : ℝ) < 2)]
  calc Real.log (L : ℝ) ≤ 2 * Real.sqrt (L : ℝ) := hlogL
    _ ≤ (ρ * (L : ℝ)) * Real.log 2 := by
        have h := mul_le_mul h4s hlog2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (le_of_lt (mul_pos hρ hLpos))
        nlinarith [h, Real.sqrt_nonneg (L : ℝ)]

end Work.KMTPlan.A6
