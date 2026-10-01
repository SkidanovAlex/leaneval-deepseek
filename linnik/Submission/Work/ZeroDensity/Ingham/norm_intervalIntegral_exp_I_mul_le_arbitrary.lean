import Mathlib

namespace Work.ZeroDensity.Ingham

open MeasureTheory

lemma norm_intervalIntegral_exp_I_mul_le_arbitrary (A B θ : ℝ) (hθ : θ ≠ 0) :
    ‖∫ t in A..B, Complex.exp (Complex.I * ((θ * t : ℝ) : ℂ))‖ ≤ 2 / |θ| := by
  set c : ℂ := Complex.I * (θ : ℂ) with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hθ)
  have hcg : ∀ t : ℝ, c * (t : ℂ) = Complex.I * ((θ * t : ℝ) : ℂ) := by
    intro t; rw [hc, Complex.ofReal_mul]; ring
  have hnormc : ‖c‖ = |θ| := by
    rw [hc, norm_mul, Complex.norm_I, one_mul, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self_eq_abs]
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => c⁻¹ * Complex.exp (c * (t : ℂ))) (Complex.exp (c * (x : ℂ))) x := by
    intro x hx
    have hg : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)))
        (Complex.exp (c * (x : ℂ)) * c) x := hg.cexp
    have h3 : HasDerivAt (fun t : ℝ => c⁻¹ * Complex.exp (c * (t : ℂ)))
        (c⁻¹ * (Complex.exp (c * (x : ℂ)) * c)) x := h2.const_mul c⁻¹
    convert h3 using 1
    rw [mul_comm (Complex.exp (c * (x:ℂ))) c, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  have hcont : Continuous (fun t : ℝ => Complex.exp (c * (t : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (c * (t : ℂ))) volume A B :=
    hcont.intervalIntegrable A B
  have hFTC : ∫ t in A..B, Complex.exp (c * (t : ℂ))
      = c⁻¹ * Complex.exp (c * (B : ℂ)) - c⁻¹ * Complex.exp (c * (A : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hfun : ∀ t : ℝ, Complex.exp (Complex.I * ((θ * t : ℝ) : ℂ)) = Complex.exp (c * (t : ℂ)) := by
    intro t; rw [hcg t]
  rw [intervalIntegral.integral_congr (fun t _ => hfun t), hFTC]
  have hEq : c⁻¹ * Complex.exp (c * (B : ℂ)) - c⁻¹ * Complex.exp (c * (A : ℂ))
      = c⁻¹ * (Complex.exp (c * (B : ℂ)) - Complex.exp (c * (A : ℂ))) := by ring
  rw [hEq]
  have hexpB : ‖Complex.exp (c * (B : ℂ))‖ = 1 := by
    rw [hcg B, Complex.norm_exp_I_mul_ofReal]
  have hexpA : ‖Complex.exp (c * (A : ℂ))‖ = 1 := by
    rw [hcg A, Complex.norm_exp_I_mul_ofReal]
  calc ‖c⁻¹ * (Complex.exp (c * (B : ℂ)) - Complex.exp (c * (A : ℂ)))‖
      ≤ ‖c⁻¹‖ * ‖Complex.exp (c * (B : ℂ)) - Complex.exp (c * (A : ℂ))‖ := norm_mul_le _ _
    _ ≤ ‖c⁻¹‖ * (‖Complex.exp (c * (B : ℂ))‖ + ‖Complex.exp (c * (A : ℂ))‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ = ‖c‖⁻¹ * (1 + 1) := by rw [norm_inv, hexpB, hexpA]
    _ = 2 / |θ| := by rw [hnormc]; ring

end Work.ZeroDensity.Ingham
