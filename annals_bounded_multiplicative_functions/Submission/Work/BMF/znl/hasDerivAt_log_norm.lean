import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.znl

/-- The real part of `p / w` equals the real inner product `⟪w, p⟫` divided by `‖w‖ ^ 2`. -/
private lemma div_re_eq_inner (w p : ℂ) :
    (p / w).re = inner ℝ w p / ‖w‖ ^ 2 := by
  rw [Complex.div_re, Complex.inner, Complex.normSq_eq_norm_sq, Complex.mul_re]
  simp only [Complex.conj_re, Complex.conj_im]
  ring

/-- Derivative of `y ↦ log ‖g y‖` for a complex-valued differentiable `g` that does not
vanish at `x`; the derivative is the real part of `g' / g x`. -/
lemma hasDerivAt_log_norm {g : ℝ → ℂ} {g' : ℂ} {x : ℝ} (hg : HasDerivAt g g' x)
    (hne : g x ≠ 0) :
    HasDerivAt (fun y => Real.log ‖g y‖) ((g' / g x).re) x := by
  have hnr : ‖g x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  -- Derivative of the modulus, obtained by composing the derivative of `‖g ·‖ ^ 2`
  -- with that of `Real.sqrt`.
  have hN : HasDerivAt (fun y => ‖g y‖) (inner ℝ (g x) g' / ‖g x‖) x := by
    have h1 : HasDerivAt (fun y => Real.sqrt (‖g y‖ ^ 2))
        (2 * inner ℝ (g x) g' / (2 * Real.sqrt (‖g x‖ ^ 2))) x :=
      (hg.norm_sq).sqrt (pow_ne_zero 2 hnr)
    rw [Real.sqrt_sq (norm_nonneg (g x))] at h1
    refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => ?_))).congr_deriv ?_
    · exact (Real.sqrt_sq (norm_nonneg (g y))).symm
    · field_simp
  -- Chain with the logarithm.
  have hlog := hN.log hnr
  have hkey : (inner ℝ (g x) g' / ‖g x‖) / ‖g x‖ = (g' / g x).re := by
    rw [div_div]
    rw [Complex.div_re, Complex.inner, Complex.normSq_eq_norm_sq, Complex.mul_re]
    simp only [Complex.conj_re, Complex.conj_im]
    ring
  rw [hkey] at hlog
  exact hlog

end Work.BMF.znl
