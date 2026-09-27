import Mathlib
import Submission.Work.EQ.normEqCurve_structure
import Submission.Work.EQ.polarPt_basic

/-!
# The polar angle of the image point under Rychlik's map, in the lower half plane

`eqT_angle_upper` and `eqT_angle_lower` together say that the polar angle of
`Q = eqT a (polarPt (-(a/2)) (ρ₁ θ) θ)` about `O₁ = -a/2` is *recovered from `Q` itself*:
writing `Q - O₁ = ρ e^{iφ}` with `ρ > 0`, the quantity `(Q - O₁).re / ‖Q - O₁‖` is exactly
`cos φ`, so that

* for `φ ∈ (0, π)` (upper half plane) we get `φ = arccos (cos φ)`, and
* for `φ ∈ (π, 2π)` (lower half plane) we get `φ = 2π - arccos (cos φ)`.

Here we prove the second statement.  Both are pure trigonometry: the only input from the
definition of a normalised equichordal curve is the positivity `0 < ρ₁` of the radial function
(which makes the polar representation of `Q - O₁` have a genuine positive length).
-/

namespace Work.EQ

open Complex

/-- Real part of a point written in polar form about a real centre. -/
lemma eqTAL_polarPt_re (c r θ : ℝ) : (polarPt c r θ).re = c + r * Real.cos θ := by
  simp only [polarPt, Complex.exp_ofReal_mul_I, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- For `φ ∈ (π, 2π)`, the angle `φ` is the reflex of `arccos (cos φ)`. -/
lemma eqTAL_eq_two_pi_sub_arccos_cos {φ : ℝ} (hφ0 : Real.pi < φ) (hφπ : φ < 2 * Real.pi) :
    φ = 2 * Real.pi - Real.arccos (Real.cos φ) := by
  have hcos : Real.arccos (Real.cos φ) = 2 * Real.pi - φ := by
    rw [← Real.cos_two_pi_sub φ]
    exact Real.arccos_cos (by linarith) (by linarith)
  rw [hcos]; ring

/-- **Polar angle of `eqT`-image, lower half plane.**  If `Q := eqT a (polarPt (-(a/2)) (ρ₁ θ) θ)`
equals `polarPt (-(a/2)) (ρ₁ φ) φ` with `φ ∈ (π, 2π)`, then `φ` is determined by `Q`:
`φ = 2π - arccos ((Q - O₁).re / ‖Q - O₁‖)`. -/
theorem eqT_angle_lower {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) {θ φ : ℝ} (hφ0 : Real.pi < φ) (hφπ : φ < 2 * Real.pi)
    (hφ : polarPt (-(a/2)) (ρ₁ φ) φ = eqT a (polarPt (-(a/2)) (ρ₁ θ) θ)) :
    φ = 2 * Real.pi - Real.arccos ((eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a).re /
      ‖eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖) := by
  obtain ⟨-, -, hpos₁, -⟩ := hC
  have hO1val : O1_sym a = ((-(a/2) : ℝ) : ℂ) := by simp only [O1_sym]; push_cast; ring
  -- `Q - O₁ = ρ₁ φ · e^{iφ}`
  have hsub : eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a
      = ((ρ₁ φ : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
    rw [← hφ, hO1val]
    simp only [polarPt]
    ring
  -- real part of `Q - O₁`
  have hre : (eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a).re = ρ₁ φ * Real.cos φ := by
    rw [hsub, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [Complex.exp_ofReal_mul_I, Complex.add_re, Complex.ofReal_re]
    rw [Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    simp
  -- length of `Q - O₁`
  have hnorm : ‖eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖ = ρ₁ φ := by
    rw [hsub, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      show ‖((ρ₁ φ : ℝ) : ℂ)‖ = |ρ₁ φ| from RCLike.norm_ofReal _, abs_of_pos (hpos₁ φ)]
  -- the quotient is `cos φ`
  have hratio : (eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a).re /
      ‖eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖ = Real.cos φ := by
    rw [hre, hnorm, mul_div_cancel_left₀ _ (ne_of_gt (hpos₁ φ))]
  rw [hratio]
  exact eqTAL_eq_two_pi_sub_arccos_cos hφ0 hφπ

end Work.EQ
