import Mathlib
import Submission.Work.EQ.normEqCurve_structure
import Submission.Work.EQ.polarPt_basic

/-!
# The polar angle of `eqT P` in the upper half plane

If `P = polarPt (-(a/2)) (ρ₁ θ) θ` is a point of a normalised equichordal curve and
`eqT a P` happens to lie at polar angle `φ ∈ (0, π)` about `O₁ = -a/2`, then `φ` is exactly
the arccosine of the cosine of the direction of `eqT a P - O₁`.  Indeed on the ray at angle
`φ` the point `eqT a P = polarPt (-(a/2)) (ρ₁ φ) φ` satisfies
`eqT a P - O₁ = ρ₁ φ · exp(iφ)`, so its real part is `ρ₁ φ cos φ` and its norm is `ρ₁ φ > 0`;
`arccos` on `[0, π]` inverts `cos`.
-/

namespace Work.EQ

open Complex

theorem eqT_angle_upper {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) {θ φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hφ : polarPt (-(a/2)) (ρ₁ φ) φ = eqT a (polarPt (-(a/2)) (ρ₁ θ) θ)) :
    φ = Real.arccos ((eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a).re /
      ‖eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖) := by
  rw [← hφ]
  have hr : 0 < ρ₁ φ := hC.2.2.1 φ
  have hsub : polarPt (-(a/2)) (ρ₁ φ) φ - O1_sym a =
      (ρ₁ φ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
    rw [O1_sym, polarPt]; push_cast; ring
  have hre : (polarPt (-(a/2)) (ρ₁ φ) φ - O1_sym a).re = ρ₁ φ * Real.cos φ := by
    rw [hsub, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, zero_mul, mul_one]
  have hnorm : ‖polarPt (-(a/2)) (ρ₁ φ) φ - O1_sym a‖ = ρ₁ φ := by
    rw [hsub, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      show ‖((ρ₁ φ : ℝ) : ℂ)‖ = |ρ₁ φ| from RCLike.norm_ofReal (ρ₁ φ), abs_of_pos hr]
  rw [hre, hnorm, mul_div_cancel_left₀ _ (ne_of_gt hr), Real.arccos_cos hφ0.le hφπ.le]

end Work.EQ
