import Mathlib

namespace Work.ZeroFreeTables

/-- For a unit complex number `b`, the real part of `b * b` is `2 * b.re ^ 2 - 1`. -/
theorem six_kernel_b_sq_re {b : ℂ} (hb : ‖b‖ = 1) : (b * b).re = 2 * b.re ^ 2 - 1 := by
  have hb2 : b.re ^ 2 + b.im ^ 2 = 1 := by
    have h := Complex.normSq_apply b
    rw [Complex.normSq_eq_norm_sq, hb] at h
    nlinarith [h]
  rw [Complex.mul_re]
  nlinarith [hb2]

theorem six_kernel_identity (k : ℝ) {a b : ℂ} (ha : a = 1 ∨ a = -1) (hb : ‖b‖ = 1) :
    (k ^ 2 + 1/2) * (a.re + 1) + 2 * k * (b.re + (a * b).re)
      + (1/2) * ((b * b).re + (a * (b * b)).re) = (1 + a.re) * (k + b.re) ^ 2 := by
  have hbb : (b * b).re = 2 * b.re ^ 2 - 1 := six_kernel_b_sq_re hb
  rcases ha with rfl | rfl
  · simp only [Complex.one_re, one_mul]
    rw [hbb]
    ring
  · simp only [Complex.neg_re, Complex.one_re, neg_mul, one_mul]
    ring

end Work.ZeroFreeTables
