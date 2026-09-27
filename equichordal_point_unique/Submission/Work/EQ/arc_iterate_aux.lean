import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_box
import Submission.Work.EQ.polarPt_basic

/-! Small shared helper lemmas for the orbit-convergence lemma
`Work.EQ.arc_iterate_tendsto_A1` and the pieces it is built from. -/

namespace Work.EQ

open Complex

set_option linter.unusedSimpArgs false

/-- Cartesian form of `polarPt c r θ = c + r e^{iθ}`. -/
theorem polarPt_eq_cartesian (c r θ : ℝ) :
    polarPt c r θ = ((c + r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [polarPt, Complex.exp_ofReal_mul_I]; push_cast; ring

theorem polarPt_re (c r θ : ℝ) : (polarPt c r θ).re = c + r * Real.cos θ := by
  rw [polarPt_eq_cartesian]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
  ring

theorem polarPt_im_eq (c r θ : ℝ) : (polarPt c r θ).im = r * Real.sin θ := by
  rw [polarPt_eq_cartesian]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one]

theorem arcPt_eq_polarPt (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) :
    arcPt a ρ₁ θ = polarPt (-(a/2)) (ρ₁ θ) θ := rfl

theorem arcPt_re (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) :
    (arcPt a ρ₁ θ).re = -(a/2) + ρ₁ θ * Real.cos θ := by
  rw [arcPt_eq_polarPt]; exact polarPt_re _ _ _

theorem arcPt_im (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) :
    (arcPt a ρ₁ θ).im = ρ₁ θ * Real.sin θ := by
  rw [arcPt_eq_polarPt]; exact polarPt_im_eq _ _ _

theorem polarPt_sub_center (c r θ : ℝ) :
    polarPt c r θ - (c : ℂ) = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  simp [polarPt]

/-- The defining expansion: `arcPt a ρ₁ θ - O₁ = ρ₁ θ · e^{iθ}` with `O₁ = -a/2`. -/
theorem arcPt_sub_center (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) :
    arcPt a ρ₁ θ - (((-(a/2)) : ℝ) : ℂ) =
      (ρ₁ θ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [arcPt_eq_polarPt]; exact polarPt_sub_center _ _ _

/-- `(w / ‖w‖) * ‖w‖ = w` in `ℂ` — including the degenerate case `w = 0`, in which the
division-by-zero convention gives `0`. -/
theorem div_norm_mul_norm (w : ℂ) :
    w / ((‖w‖ : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ) = w := by
  rcases eq_or_ne (‖w‖) 0 with h | h
  · have hw : w = 0 := norm_eq_zero.mp h
    subst hw; simp
  · exact div_mul_cancel₀ w (Complex.ofReal_ne_zero.mpr h)

/-- Addition formula for the unit circle, in the direction needed for the strict-increase
argument: `e^{iψ} · e^{-iθ} = e^{i(ψ-θ)}`. -/
theorem exp_mul_I_sub (ψ θ : ℝ) :
    Complex.exp ((ψ : ℂ) * Complex.I) * Complex.exp (-((θ : ℂ) * Complex.I)) =
      Complex.exp (((ψ - θ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

end Work.EQ
