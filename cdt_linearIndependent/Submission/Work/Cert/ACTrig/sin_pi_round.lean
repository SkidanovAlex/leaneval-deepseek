import Mathlib

namespace Work.Cert.ACTrig

theorem sin_pi_round (x : ℝ) : ∃ k : ℤ, |x - k| ≤ |Real.sin (Real.pi * x)| / 2 := by
  refine ⟨round x, ?_⟩
  -- the nearest integer is within `1/2` of `x`
  have hx : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
  -- `sin (π x)` coincides up to sign with `sin (π (x - round x))`
  have hsin : |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * (x - round x))| := by
    have heq : Real.pi * x = Real.pi * (x - (round x : ℝ)) + (round x : ℝ) * Real.pi := by ring
    rw [heq, Real.sin_add_int_mul_pi, abs_mul, abs_zpow,
      show |(-1 : ℝ)| = 1 by simp, one_zpow, one_mul]
  -- Jordan's inequality in the form `2 * |t| ≤ |sin (π t)|` for `|t| ≤ 1/2`
  have hJ : 2 * |x - (round x : ℝ)| ≤ |Real.sin (Real.pi * (x - round x))| := by
    have hπ : |Real.pi * (x - (round x : ℝ))| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos, hx]
    have hJ' := Real.mul_abs_le_abs_sin hπ
    rw [abs_mul, abs_of_pos Real.pi_pos] at hJ'
    have h2 : 2 / Real.pi * (Real.pi * |x - (round x : ℝ)|) = 2 * |x - (round x : ℝ)| := by
      field_simp
    linarith
  rw [hsin]
  linarith

end Work.Cert.ACTrig
