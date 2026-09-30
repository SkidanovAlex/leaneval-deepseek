import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Key real inequality: if `b ∈ (-π, π]` and `n` is an integer, then adding `2πn` to `b`
does not decrease the square. This is the analytic heart of the fact that the principal
branch of the logarithm has minimal modulus among all logarithms. -/
lemma sq_le_sq_add_two_pi_mul (b : ℝ) (hb1 : -Real.pi < b) (hb2 : b ≤ Real.pi) (n : ℤ) :
    b * b ≤ (b + 2 * Real.pi * n) * (b + 2 * Real.pi * n) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · -- n ≤ -1 : both factors `2πn` and `2b + 2πn` are nonpositive
    have hn1 : (n : ℝ) ≤ -1 := by
      have : n ≤ -1 := by omega
      exact_mod_cast this
    have hbn : b + Real.pi * n ≤ 0 := by nlinarith [Real.pi_pos, hb2, hn1]
    have h1 : 2 * Real.pi * n ≤ 0 := by nlinarith [Real.pi_pos, hn1]
    have h2 : 2 * b + 2 * Real.pi * n ≤ 0 := by nlinarith [hbn]
    have h3 := mul_nonneg_of_nonpos_of_nonpos h1 h2
    nlinarith [h3]
  · subst hn; simp
  · -- n ≥ 1 : both factors `2πn` and `2b + 2πn` are nonnegative
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : (1 : ℤ) ≤ n := by omega
      exact_mod_cast this
    have hbn : 0 ≤ b + Real.pi * n := by nlinarith [Real.pi_pos, hb1, hn1]
    have h1 : 0 ≤ 2 * Real.pi * n := by nlinarith [Real.pi_pos, hn1]
    have h2 : 0 ≤ 2 * b + 2 * Real.pi * n := by nlinarith [hbn]
    have h3 := mul_nonneg h1 h2
    nlinarith [h3]

/-- The principal logarithm has least norm among all logarithms: if `Complex.exp w = z` then
`‖Complex.log z‖ ≤ ‖w‖`. -/
theorem kummer_log_norm_le {z w : ℂ} (h : Complex.exp w = z) : ‖Complex.log z‖ ≤ ‖w‖ := by
  -- `z ≠ 0`, so `exp w = z = exp (log z)` and hence `w = log z + 2πi n` for some integer `n`.
  have hz : z ≠ 0 := by rw [← h]; exact Complex.exp_ne_zero w
  have hexp : Complex.exp w = Complex.exp (Complex.log z) := by rw [h, Complex.exp_log hz]
  rw [Complex.exp_eq_exp_iff_exists_int] at hexp
  obtain ⟨n, hn⟩ := hexp
  -- Reading off real and imaginary parts of the relation `w = log z + 2πi n`.
  have hnre : w.re = (Complex.log z).re := by rw [hn]; simp
  have hnim : w.im = (Complex.log z).im + 2 * Real.pi * n := by rw [hn]; simp; ring
  -- The imaginary part of `log z` lies in `(-π, π]`.
  have hkey : (Complex.log z).im * (Complex.log z).im ≤ w.im * w.im := by
    rw [hnim]
    exact sq_le_sq_add_two_pi_mul (Complex.log z).im (Complex.neg_pi_lt_log_im z)
      (Complex.log_im_le_pi z) n
  -- Compare squared norms and conclude using nonnegativity.
  have hsq : ‖Complex.log z‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hnre]
    nlinarith [hkey]
  have h1 : (0 : ℝ) ≤ ‖Complex.log z‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have h3 := sq_le_sq.mp hsq
  rwa [abs_of_nonneg h1, abs_of_nonneg h2] at h3

end Work.BW
