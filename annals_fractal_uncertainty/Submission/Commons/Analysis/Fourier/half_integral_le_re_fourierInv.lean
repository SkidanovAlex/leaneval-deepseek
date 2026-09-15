import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Real.Pi.Bounds

namespace Commons.Analysis.Fourier

open scoped Real

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- The real part of `𝐞 θ • r` for a real number `r`: it equals `cos (2 * π * θ) * r`,
where `𝐞` is the standard additive character `x ↦ exp (2 * π * x * I)`. -/
lemma fourierChar_smul_ofReal_re (θ r : ℝ) :
    (((Real.fourierChar θ : Circle) : ℂ) * (r : ℂ)).re = Real.cos (2 * π * θ) * r := by
  rw [Real.fourierChar_apply, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- **Lower bound for the inverse Fourier transform of a small bump.**  If `ρ ≥ 0` is an integrable
real function on `ℝⁿ` supported in the ball of radius `1/8`, then the inverse Fourier transform of
`ρ` is bounded below by `(1/2) * ∫ ρ` on the unit ball.  Indeed, `𝓕⁻ρ u = ∫ w, ρ w * exp(2πi⟪w,u⟫)`,
whose real part is `∫ w, ρ w * cos(2π⟪w,u⟫) ≥ ∫ w, ρ w * cos(π/4) ≥ (1/2) ∫ w, ρ w` whenever
`‖u‖ ≤ 1`. -/
theorem half_integral_le_re_fourierInv {n : ℕ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρnn : ∀ w, 0 ≤ ρ w) (hρint : Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hρsupp : ∀ w, 1 / 8 < ‖w‖ → ρ w = 0)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ ≤ 1) :
    (1 / 2) * (∫ w, ρ w) ≤ (𝓕⁻ (fun w => ((ρ w : ℝ) : ℂ)) u).re := by
  -- The real part of the integrand is `cos (2 * π * ⟪v, u⟫) * ρ v`.
  have hre : ∀ v, (𝐞 ⟪v, u⟫ • ((ρ v : ℝ) : ℂ)).re = Real.cos (2 * π * ⟪v, u⟫) * ρ v := by
    intro v
    rw [Circle.smul_def, smul_eq_mul]
    exact fourierChar_smul_ofReal_re _ _
  -- Integrability of the integrand of the inverse Fourier transform.
  have hfint : Integrable (fun v => 𝐞 ⟪v, u⟫ • ((ρ v : ℝ) : ℂ))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h1 : Integrable (fun v => ((ρ v : ℝ) : ℂ)) volume := hρint.ofReal
    have h2 := (Real.fourierIntegral_convergent_iff
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (f := fun v => ((ρ v : ℝ) : ℂ)) (-u)).mpr h1
    simpa using h2
  -- Pointwise lower bound.
  have hpoint : ∀ v, (1 / 2) * ρ v ≤ (𝐞 ⟪v, u⟫ • ((ρ v : ℝ) : ℂ)).re := by
    intro v
    by_cases h : ρ v = 0
    · simp [h]
    · -- `ρ v ≠ 0` forces `‖v‖ ≤ 1/8`, hence `|⟪v, u⟫| ≤ 1/8` and `|2 * π * ⟪v, u⟫| ≤ 1`.
      have hv : ‖v‖ ≤ 1 / 8 := le_of_not_gt (fun hc => h (hρsupp v hc))
      have hinner : |⟪v, u⟫| ≤ 1 / 8 := by
        calc |⟪v, u⟫| ≤ ‖v‖ * ‖u‖ := abs_real_inner_le_norm v u
          _ ≤ (1 / 8) * 1 := by gcongr
          _ = 1 / 8 := by norm_num
      have hθ : |2 * π * ⟪v, u⟫| ≤ 1 := by
        rw [abs_mul]
        have h1 : |2 * π| = 2 * π := by rw [abs_of_pos]; positivity
        rw [h1]
        calc (2 * π) * |⟪v, u⟫| ≤ (2 * π) * (1 / 8) := by
              apply mul_le_mul_of_nonneg_left hinner; positivity
          _ = π / 4 := by ring
          _ ≤ 1 := by nlinarith [Real.pi_lt_four]
      have hcos : (1 : ℝ) / 2 ≤ Real.cos (2 * π * ⟪v, u⟫) := by
        have h1 : 1 - (2 * π * ⟪v, u⟫) ^ 2 / 2 ≤ Real.cos (2 * π * ⟪v, u⟫) :=
          Real.one_sub_sq_div_two_le_cos
        have h2 : (2 * π * ⟪v, u⟫) ^ 2 ≤ 1 := by
          rwa [sq_le_one_iff_abs_le_one]
        nlinarith [h1, h2]
      rw [hre v]
      exact mul_le_mul_of_nonneg_right hcos (hρnn v)
  -- Bring the real part inside the integral.
  have hre_int : (∫ v, 𝐞 ⟪v, u⟫ • ((ρ v : ℝ) : ℂ)).re
      = ∫ v, (𝐞 ⟪v, u⟫ • ((ρ v : ℝ) : ℂ)).re := by
    have hclm := Complex.reCLM.integral_comp_comm hfint
    simp only [Complex.reCLM_apply] at hclm
    exact hclm.symm
  rw [Real.fourierInv_eq]
  rw [hre_int]
  rw [← integral_const_mul (1 / 2 : ℝ) ρ]
  exact integral_mono (hρint.const_mul (1 / 2)) hfint.re hpoint

end Commons.Analysis.Fourier