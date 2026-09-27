import Mathlib
import Submission.Work.Analysis.Complex.det_mul_complex

/-!
# The change of variables formula for a holomorphic map (`∫ F = ∫ ‖τ'‖² · F ∘ τ`)

For an injective holomorphic `τ` on an open `U ⊆ ℂ` and `F` continuous with compact support in
`τ '' U`,
  `∫ w, F w = ∫ z in U, ‖deriv τ z‖ ^ 2 * F (τ z)`.
This is the conformal invariance of the Dirichlet density `⟨∇u, ∇v⟩ dA = ⟨∇(u∘τ), ∇(v∘τ)⟩ · |τ'|² dA`,
i.e. the statement that `⟨∇u,∇v⟩ dA` is a well-defined density on a Riemann surface; it is the input
of the chart-wise Green-identity proof of the symmetry of the Green function
(`Submission/Work/Drive/NOTES_energyRoute_chartwise.md`).
-/

open MeasureTheory
open Complex

namespace Work.Analysis.Complex

theorem integral_conformal_change_of_variables (τ : ℂ → ℂ) (hτ : Differentiable ℂ τ) {U : Set ℂ}
    (hU : IsOpen U) (hinj : Set.InjOn τ U) {F : ℂ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hsupp : tsupport F ⊆ τ '' U) :
    ∫ w : ℂ, F w = ∫ z in U, ‖deriv τ z‖ ^ 2 * F (τ z) := by
  have hzero : ∀ w, w ∉ τ '' U → F w = 0 := fun w hw => by
    by_contra h
    exact hw (hsupp (subset_tsupport F (by rwa [Function.mem_support])))
  have h1 : ∫ w : ℂ, F w = ∫ w in τ '' U, F w :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hff : ∀ x : ℂ, fderiv ℝ τ x
      = (((fderiv ℂ τ x : ℂ →L[ℂ] ℂ)).restrictScalars ℝ : ℂ →L[ℝ] ℂ) :=
    fun x => (((hτ x).hasFDerivAt).restrictScalars ℝ).fderiv
  have hf' : ∀ x ∈ U, HasFDerivWithinAt τ (fderiv ℝ τ x) U x := fun x hx => by
    rw [hff x]
    exact (((hτ x).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  have h2 : ∫ w in τ '' U, F w = ∫ z in U, |(fderiv ℝ τ z).det| • F (τ z) :=
    integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hU.measurableSet hf' hinj F
  rw [h1, h2]
  refine setIntegral_congr_fun hU.measurableSet fun z hz => ?_
  have hdet : (fderiv ℝ τ z).det = ‖deriv τ z‖ ^ 2 := by
    have hC : (fderiv ℂ τ z : ℂ →L[ℂ] ℂ)
        = ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv τ z) := by
      apply ContinuousLinearMap.ext
      intro w
      have hAw : (fderiv ℂ τ z : ℂ →L[ℂ] ℂ) w = w • deriv τ z := by
        rw [show w = w • (1 : ℂ) by simp, map_smul, fderiv_apply_one_eq_deriv]
        simp
      rw [hAw, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul]
    rw [hff z, hC]
    exact det_smulRight_one_complex (deriv τ z)
  rw [hdet, abs_of_nonneg (by positivity), smul_eq_mul]

end Work.Analysis.Complex
