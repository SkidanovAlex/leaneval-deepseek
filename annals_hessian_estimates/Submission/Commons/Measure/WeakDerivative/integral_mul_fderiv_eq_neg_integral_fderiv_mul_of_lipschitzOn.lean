import Mathlib
import Submission.Commons.Measure.WeakDerivative.integral_mul_fderiv_eq_neg_integral_fderiv_mul

namespace Commons.Measure.WeakDerivative

open MeasureTheory Metric in
open scoped RealInnerProductSpace InnerProductSpace Topology in
theorem integral_mul_fderiv_eq_neg_integral_fderiv_mul_of_lipschitzOn {n : ℕ}
    {u φ : EuclideanSpace ℝ (Fin n) → ℝ} {C : NNReal} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : IsOpen s) (hu : LipschitzOnWith C u s) (hsub : tsupport φ ⊆ s)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, u x * (fderiv ℝ φ x) v = -∫ x, φ x * (fderiv ℝ u x) v := by
  obtain ⟨g, hg, hgu⟩ := hu.extend_real
  have key := integral_mul_fderiv_eq_neg_integral_fderiv_mul (n := n) hg hφ hφc v
  have h1 : ∫ x, u x * (fderiv ℝ φ x) v = ∫ x, g x * (fderiv ℝ φ x) v :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show u x * (fderiv ℝ φ x) v = g x * (fderiv ℝ φ x) v
      by_cases hx : x ∈ tsupport φ
      · rw [hgu (hsub hx)]
      · rw [fderiv_of_notMem_tsupport ℝ hx]; simp)
  have h2 : ∫ x, φ x * (fderiv ℝ u x) v = ∫ x, φ x * (fderiv ℝ g x) v :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show φ x * (fderiv ℝ u x) v = φ x * (fderiv ℝ g x) v
      by_cases hx : x ∈ tsupport φ
      · have hfg : fderiv ℝ u x = fderiv ℝ g x :=
          (hgu.eventuallyEq_of_mem (hs.mem_nhds (hsub hx))).fderiv_eq
        rw [hfg]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul])
  rw [h1, h2, key]

end Commons.Measure.WeakDerivative
