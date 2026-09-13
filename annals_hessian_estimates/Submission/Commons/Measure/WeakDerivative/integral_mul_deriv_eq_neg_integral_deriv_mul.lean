import Mathlib.Analysis.Calculus.Rademacher

namespace Commons.Measure.WeakDerivative

open MeasureTheory in
theorem integral_mul_deriv_eq_neg_integral_deriv_mul {f φ : ℝ → ℝ} {C : NNReal}
    (hf : LipschitzWith C f) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ x, f x * deriv φ x = -∫ x, φ x * deriv f x := by
  obtain ⟨D, hφD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
  -- Integration by parts for line derivatives of Lipschitz functions.
  have key : ∫ x, lineDeriv ℝ f x (1 : ℝ) * φ x
      = ∫ x, lineDeriv ℝ φ x (-1 : ℝ) * f x :=
    LipschitzWith.integral_lineDeriv_mul_eq hf hφD hφc 1
  -- Almost everywhere `lineDeriv ℝ f x 1 = deriv f x` (Rademacher).
  have hf_ae : (fun x => lineDeriv ℝ f x (1 : ℝ) * φ x)
      =ᵐ[volume] (fun x => deriv f x * φ x) := by
    filter_upwards [hf.ae_differentiableAt_real] with x hx
    rw [hx.lineDeriv_eq_fderiv, fderiv_apply_one_eq_deriv]
  -- Everywhere `lineDeriv ℝ φ x (-1) = -deriv φ x`.
  have hφ_all : ∀ x, lineDeriv ℝ φ x (-1 : ℝ) = - deriv φ x := by
    intro x
    rw [(hφ.differentiable_one.differentiableAt).lineDeriv_eq_fderiv, map_neg,
      fderiv_apply_one_eq_deriv]
  have hφ_ae : (fun x => lineDeriv ℝ φ x (-1 : ℝ) * f x)
      =ᵐ[volume] (fun x => (-deriv φ x) * f x) :=
    Filter.Eventually.of_forall fun x => by
      change lineDeriv ℝ φ x (-1 : ℝ) * f x = (-deriv φ x) * f x
      rw [hφ_all x]
  rw [integral_congr_ae hf_ae, integral_congr_ae hφ_ae] at key
  simp_rw [neg_mul] at key
  rw [integral_neg] at key
  have hA : ∫ x, deriv f x * φ x = ∫ x, φ x * deriv f x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hB : ∫ x, deriv φ x * f x = ∫ x, f x * deriv φ x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [hA, hB] at key
  linarith [key]

end Commons.Measure.WeakDerivative