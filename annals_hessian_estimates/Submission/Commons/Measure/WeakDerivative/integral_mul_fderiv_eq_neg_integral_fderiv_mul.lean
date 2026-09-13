import Mathlib.Analysis.Calculus.Rademacher
import Submission.Commons.Measure.WeakDerivative.integral_mul_deriv_eq_neg_integral_deriv_mul

namespace Commons.Measure.WeakDerivative

open MeasureTheory in
open scoped RealInnerProductSpace InnerProductSpace Topology in
theorem integral_mul_fderiv_eq_neg_integral_fderiv_mul {n : ℕ}
    {u φ : EuclideanSpace ℝ (Fin n) → ℝ} {C : NNReal}
    (hu : LipschitzWith C u) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, u x * (fderiv ℝ φ x) v = -∫ x, φ x * (fderiv ℝ u x) v := by
  obtain ⟨D, hφD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
  -- Integration by parts for line derivatives of Lipschitz functions.
  have key : ∫ x, lineDeriv ℝ u x v * φ x = ∫ x, lineDeriv ℝ φ x (-v) * u x :=
    hu.integral_lineDeriv_mul_eq hφD hφc v
  -- Almost everywhere `lineDeriv ℝ u x v = (fderiv ℝ u x) v` (Rademacher).
  have hu_ae : (fun x => lineDeriv ℝ u x v * φ x)
      =ᵐ[volume] (fun x => (fderiv ℝ u x) v * φ x) := by
    filter_upwards [hu.ae_differentiableAt] with x hx
    rw [hx.lineDeriv_eq_fderiv]
  -- Everywhere `lineDeriv ℝ φ x (-v) = -((fderiv ℝ φ x) v)`.
  have hφ_all : ∀ x, lineDeriv ℝ φ x (-v) = -((fderiv ℝ φ x) v) := by
    intro x
    rw [(hφ.differentiable_one.differentiableAt).lineDeriv_eq_fderiv, map_neg]
  have hφ_ae : (fun x => lineDeriv ℝ φ x (-v) * u x)
      =ᵐ[volume] (fun x => (-(fderiv ℝ φ x) v) * u x) :=
    Filter.Eventually.of_forall fun x => by
      change lineDeriv ℝ φ x (-v) * u x = (-(fderiv ℝ φ x) v) * u x
      rw [hφ_all x]
  rw [integral_congr_ae hu_ae, integral_congr_ae hφ_ae] at key
  simp_rw [neg_mul] at key
  rw [integral_neg] at key
  have hA : ∫ x, (fderiv ℝ u x) v * φ x = ∫ x, φ x * (fderiv ℝ u x) v :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hB : ∫ x, (fderiv ℝ φ x) v * u x = ∫ x, u x * (fderiv ℝ φ x) v :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [hA, hB] at key
  linarith [key]

end Commons.Measure.WeakDerivative