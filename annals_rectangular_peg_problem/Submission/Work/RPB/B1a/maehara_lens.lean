import Mathlib

namespace Work.RPB.B1a

theorem maehara_lens (p : ℂ) (h1 : ‖p‖ ≤ 1) (h2 : ‖p - 1‖ ≤ 1) :
    -(1:ℝ) ≤ (2*p - 1).re ∧ (2*p - 1).re ≤ 1 ∧
    -(2:ℝ) ≤ (2*p - 1).im ∧ (2*p - 1).im ≤ 2 ∧
    ((2*p - 1).re = 1 → p = 1) ∧ ((2*p - 1).re = -1 → p = 0) ∧
    (2*p - 1).im ≠ 2 ∧ (2*p - 1).im ≠ -2 := by
  -- Squared-norm form of the two disk conditions.
  have h1s : Complex.normSq p ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg p, h1]
  have h2s : Complex.normSq (p - 1) ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (p - 1), h2]
  rw [Complex.normSq_apply] at h1s h2s
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h2s
  rw [sub_zero] at h2s
  -- Coordinates of the affine image `2 * p - 1`.
  have hr : (2*p - 1).re = 2 * p.re - 1 := by simp [Complex.sub_re, Complex.mul_re]
  have hi : (2*p - 1).im = 2 * p.im := by simp [Complex.sub_im, Complex.mul_im]
  -- The lens sits in the box `0 ≤ re ≤ 1`, `-1 ≤ im ≤ 1`.
  have hx0 : 0 ≤ p.re := by nlinarith [h2s, sq_nonneg p.re, sq_nonneg p.im]
  have hx1 : p.re ≤ 1 := by nlinarith [h1s, hx0, sq_nonneg p.im]
  have hy0 : -1 ≤ p.im := by nlinarith [h1s, sq_nonneg p.re]
  have hy1 : p.im ≤ 1 := by nlinarith [h1s, sq_nonneg p.re]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hr, hi]
  · linarith
  · linarith
  · linarith
  · linarith
  · intro h
    have hx : p.re = 1 := by linarith
    have hy : p.im = 0 := by nlinarith [h1s, hx]
    exact Complex.ext (by simpa using hx) (by simpa using hy)
  · intro h
    have hx : p.re = 0 := by linarith
    have hy : p.im = 0 := by nlinarith [h2s, hx]
    exact Complex.ext (by simpa using hx) (by simpa using hy)
  · intro h; exfalso; nlinarith [h1s, h2s, h]
  · intro h; exfalso; nlinarith [h1s, h2s, h]

end Work.RPB.B1a
