import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Flower

open Complex

/-- The branch defect of the complex logarithm with respect to division is bounded by `2 * π`:
for nonzero `a b : ℂ` one has `‖log a - log b - log (a / b)‖ ≤ 2 * π`.

Indeed `log a - log b - log (a / b)` is purely imaginary with imaginary part
`arg a - arg b - arg (a / b)`, which is an integer multiple of `2 * π` lying in
the open interval `(-3π, 3π)` by the standard bounds on `arg`. -/
theorem norm_log_sub_log_sub_log_div_le {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖Complex.log a - Complex.log b - Complex.log (a / b)‖ ≤ 2 * Real.pi := by
  have hab : a / b ≠ 0 := div_ne_zero ha hb
  -- `exp` of the defect is `1`, so the defect is an integer multiple of `2 * π * I`.
  have hexp : Complex.exp (Complex.log a - Complex.log b - Complex.log (a / b)) = 1 := by
    rw [sub_sub, Complex.exp_sub, Complex.exp_add, Complex.exp_log ha, Complex.exp_log hb,
      Complex.exp_log hab]
    field_simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  -- Its imaginary part, computed two ways.
  have him1 : (Complex.log a - Complex.log b - Complex.log (a / b)).im
      = Complex.arg a - Complex.arg b - Complex.arg (a / b) := by
    rw [Complex.sub_im, Complex.sub_im, Complex.log_im, Complex.log_im, Complex.log_im]
  have him2 : (Complex.log a - Complex.log b - Complex.log (a / b)).im
      = (n : ℝ) * (2 * Real.pi) := by
    rw [hn]
    simp [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im]
  have ht : (n : ℝ) * (2 * Real.pi)
      = Complex.arg a - Complex.arg b - Complex.arg (a / b) := by
    rw [← him2, him1]
  -- The imaginary part is bounded by `3 * π` in absolute value.
  have h3 : |(n : ℝ) * (2 * Real.pi)| < 3 * Real.pi := by
    rw [ht]
    have h1 : |Complex.arg a - Complex.arg b| < 2 * Real.pi := Complex.abs_arg_sub_arg_lt a b
    have h2 : |Complex.arg (a / b)| ≤ Real.pi := Complex.abs_arg_le_pi _
    calc |Complex.arg a - Complex.arg b - Complex.arg (a / b)|
        = |(Complex.arg a - Complex.arg b) - Complex.arg (a / b)| := by ring_nf
      _ ≤ |Complex.arg a - Complex.arg b| + |Complex.arg (a / b)| := abs_sub _ _
      _ < 2 * Real.pi + Real.pi := by linarith
      _ = 3 * Real.pi := by ring
  have h3' : |(n : ℝ)| * (2 * Real.pi) < 3 * Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h3
    exact h3
  -- Hence the integer `n` satisfies `|n| ≤ 1`.
  have h5 : |(n : ℝ)| < 3 / 2 := by nlinarith [h3', Real.pi_pos]
  have habs_n : |(n : ℝ)| ≤ 1 := by
    have hlt2 : (n : ℝ) < 2 := by
      have := lt_of_le_of_lt (le_abs_self (n : ℝ)) h5; linarith
    have hgt2 : (-2 : ℝ) < (n : ℝ) := by
      have := lt_of_lt_of_le (by linarith : (-3 / 2 : ℝ) < -|(n : ℝ)|) (neg_abs_le (n : ℝ))
      linarith
    have hn_lt : n < 2 := by exact_mod_cast hlt2
    have hn_gt : -2 < n := by exact_mod_cast hgt2
    have hb1 : n ≤ 1 := by omega
    have hb2 : -1 ≤ n := by omega
    rw [abs_le]
    exact ⟨by exact_mod_cast hb2, by exact_mod_cast hb1⟩
  -- Finally the norm of the defect is `|n| * 2 * π`.
  have hnorm : ‖Complex.log a - Complex.log b - Complex.log (a / b)‖
      = |(n : ℝ)| * (2 * Real.pi) := by
    rw [hn]
    simp [Complex.norm_intCast, Complex.norm_I]
  rw [hnorm]
  calc |(n : ℝ)| * (2 * Real.pi) ≤ 1 * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right habs_n (by positivity)
      _ = 2 * Real.pi := by ring

end Work.FatouCoord.Flower
