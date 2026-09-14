import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.TotallySplit

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory
open scoped Real BigOperators

/-- Change of variables for a diagonal positive linear map applied to a measurable set `K`:
`∫_{D_u K} exp(-π‖x‖²) dx = ∫_K exp(∑ᵢ uᵢ) · exp(-π ‖D_u y‖²) dy`,
where `D_u y = WithLp.toLp 2 (fun i => exp (u i) * y i)`.
Equivalently the right-hand side is `∫_K exp(∑ᵢ uᵢ) · exp(-π ∑ᵢ (exp (uᵢ) * yᵢ)²) dy`. -/
theorem integral_diag_image {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (u : Fin n → ℝ) :
    (∫ x in (fun x : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (fun i => Real.exp (u i) * x i)) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∫ y in K, Real.exp (∑ i, u i) *
          Real.exp (-Real.pi * ∑ i, (Real.exp (u i) * y i) ^ 2) := by
  classical
  -- The diagonal (positive) linear map `D`, written as a composition of the
  -- coordinate scaling map on `Fin n → ℝ` with the linear equiv between
  -- `EuclideanSpace ℝ (Fin n)` and `Fin n → ℝ`.
  let D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => WithLp.toLp 2 (fun i => Real.exp (u i) * x i)
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let L' : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i => (LinearMap.mulLeft ℝ (Real.exp (u i))).comp (LinearMap.proj i))
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (e.symm : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).comp
      (L'.comp (e : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ)))
  have hL : ∀ x : EuclideanSpace ℝ (Fin n),
      L x = WithLp.toLp 2 (fun i => Real.exp (u i) * x i) := by
    intro x
    have h1 : e x = (fun i => x i) := by
      ext i
      show (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)) x i = x i
      simp [WithLp.linearEquiv_apply]
    have h2 : ∀ v : Fin n → ℝ, e.symm v = WithLp.toLp 2 v := by
      intro v
      apply WithLp.ofLp_injective 2
      show ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm v).ofLp = v
      simp [WithLp.linearEquiv_symm_apply]
    show e.symm (L' (e x)) = WithLp.toLp 2 (fun i => Real.exp (u i) * x i)
    rw [h2, h1]
    congr 1
  -- The determinant of `D` is `∏ i, exp (u i) = exp (∑ i, u i)`.
  have hdet : LinearMap.det L = Real.exp (∑ i, u i) := by
    have hdet' : LinearMap.det L' = Real.exp (∑ i, u i) := by
      rw [LinearMap.det_pi, Real.exp_sum]; simp
    rw [← hdet']
    exact LinearMap.det_conj L' e.symm
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := L.toContinuousLinearMap
  have hA : (⇑A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = ⇑L :=
    LinearMap.coe_toContinuousLinearMap' (f := L)
  have hAD : ⇑A = D := by
    funext x
    rw [congrFun hA x]
    exact hL x
  have hAdet : A.det = Real.exp (∑ i, u i) := by
    rw [show A.det = LinearMap.det L from LinearMap.det_toContinuousLinearMap (f := L), hdet]
  have hInj : Set.InjOn D K := by
    have hinj : Function.Injective D := by
      intro a b hab
      apply WithLp.ofLp_injective 2
      funext i
      have hc := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp i) hab
      simp only [D] at hc
      exact mul_left_cancel₀ (Real.exp_ne_zero (u i)) hc
    exact hinj.injOn
  have hf' : ∀ x ∈ K, HasFDerivWithinAt D A K x := by
    intro x _
    have h := A.hasFDerivAt (x := x)
    rw [hAD] at h
    exact h.hasFDerivWithinAt
  rw [show (fun x : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (fun i => Real.exp (u i) * x i)) = D from rfl]
  -- Change of variables for the differentiable (linear) map `D`.
  rw [integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hK hf' hInj
      (fun x => Real.exp (-Real.pi * ‖x‖ ^ 2))]
  apply setIntegral_congr_fun hK
  intro y _
  beta_reduce
  rw [hAdet, abs_of_pos (Real.exp_pos _), smul_eq_mul]
  congr 1
  show Real.exp (-Real.pi * ‖D y‖ ^ 2) = Real.exp (-Real.pi * ∑ i, (Real.exp (u i) * y i) ^ 2)
  rw [EuclideanSpace.real_norm_sq_eq]

end Commons.Analysis.GaussianMeasure