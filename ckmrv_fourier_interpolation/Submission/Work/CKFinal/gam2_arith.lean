import Mathlib

namespace Work.CKFinal

/-- Norm-square of `z + c` for a real `c`, in terms of real and imaginary parts. -/
lemma norm_sq_add_real (z : ℂ) (c : ℝ) :
    ‖z + (c : ℂ)‖ ^ 2 = (z.re + c) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem gam2_arith (z : ℂ) (him : 0 < z.im)
    (h14 : (1 : ℝ) / 4 < ‖z + (1 / 4 : ℂ)‖)
    (h34 : (1 : ℝ) / 4 < ‖z + (3 / 4 : ℂ)‖)
    (hh : ‖z + (1 / 2 : ℂ)‖ < 1 / 2) :
    2 * (z.re ^ 2 + z.im ^ 2) + z.re > 0 ∧
    2 * (z.re ^ 2 + z.im ^ 2) + 3 * z.re + 1 > 0 ∧
    z.re ^ 2 + z.im ^ 2 + z.re < 0 ∧ z.re < 0 ∧
    (1 + z.re) ^ 2 + z.im ^ 2 > 0 := by
  -- Rewrite the three complex centres as casts of real numbers.
  have e1 : (1 / 4 : ℂ) = (((1 : ℝ) / 4 : ℝ) : ℂ) := by norm_num
  have e3 : (3 / 4 : ℂ) = (((3 : ℝ) / 4 : ℝ) : ℂ) := by norm_num
  have e2 : (1 / 2 : ℂ) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by norm_num
  rw [e1] at h14
  rw [e3] at h34
  rw [e2] at hh
  -- Square the three norm inequalities (both sides are nonnegative).
  have h14sq : ((1 : ℝ) / 4) ^ 2 < ‖z + (((1 : ℝ) / 4 : ℝ) : ℂ)‖ ^ 2 :=
    pow_lt_pow_left₀ h14 (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
  have h34sq : ((1 : ℝ) / 4) ^ 2 < ‖z + (((3 : ℝ) / 4 : ℝ) : ℂ)‖ ^ 2 :=
    pow_lt_pow_left₀ h34 (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
  have hhsq : ‖z + (((1 : ℝ) / 2 : ℝ) : ℂ)‖ ^ 2 < ((1 : ℝ) / 2) ^ 2 :=
    pow_lt_pow_left₀ hh (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)
  rw [norm_sq_add_real z (1 / 4)] at h14sq
  rw [norm_sq_add_real z (3 / 4)] at h34sq
  rw [norm_sq_add_real z (1 / 2)] at hhsq
  -- Expand each conjunct and close by linear arithmetic.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith [h14sq, h34sq, hhsq, him,
      sq_nonneg z.re, sq_nonneg z.im, sq_nonneg (1 + z.re)]

end Work.CKFinal
