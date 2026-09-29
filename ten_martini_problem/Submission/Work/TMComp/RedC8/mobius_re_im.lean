import Mathlib

namespace Work.TMComp.RedC8

/-- Real and imaginary parts of the Möbius transformation `ζ ↦ (R + ζ)/(R - ζ)` for real `R`. -/
lemma mobius_re_im (R : ℝ) (ζ : ℂ) (h : (R : ℂ) - ζ ≠ 0) :
    (((R : ℂ) + ζ) / ((R : ℂ) - ζ)).re = (R ^ 2 - ‖ζ‖ ^ 2) / ‖(R : ℂ) - ζ‖ ^ 2 ∧
      (((R : ℂ) + ζ) / ((R : ℂ) - ζ)).im = 2 * R * ζ.im / ‖(R : ℂ) - ζ‖ ^ 2 := by
  have hns : Complex.normSq ((R : ℂ) - ζ) ≠ 0 := by
    intro hh
    exact h (Complex.normSq_eq_zero.mp hh)
  constructor
  · rw [Complex.div_re, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  · rw [Complex.div_im, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring

end Work.TMComp.RedC8
