import Mathlib
import Submission.Work.EQ.Defs

namespace Work.EQ

theorem polarPt_basic {c r θ : ℝ} (hr : 0 < r) :
    (polarPt c r θ).im = r * Real.sin θ ∧
      polarPt c r θ - (c : ℂ) = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∧
      ‖polarPt c r θ - (c : ℂ)‖ = r ∧ polarPt c r θ ≠ (c : ℂ) := by
  -- explicit Cartesian form of the point
  have hexp : polarPt c r θ =
      ((c + r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [polarPt, Complex.exp_ofReal_mul_I]
    push_cast
    ring
  have him : (polarPt c r θ).im = r * Real.sin θ := by
    rw [hexp, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hdiff : polarPt c r θ - (c : ℂ) = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [polarPt]
  have hnorm : ‖polarPt c r θ - (c : ℂ)‖ = r := by
    rw [hdiff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      show ‖(r : ℂ)‖ = |r| from by simp, abs_of_pos hr]
  have hne : polarPt c r θ ≠ (c : ℂ) := by
    intro h
    have h0 : ‖polarPt c r θ - (c : ℂ)‖ = 0 := by simp [h]
    rw [hnorm] at h0
    exact absurd h0 (ne_of_gt hr)
  exact ⟨him, hdiff, hnorm, hne⟩

end Work.EQ
