import Mathlib
import Submission.Work.Projection.Basic

open scoped Manifold ContDiff
open Topology

namespace Work.Projection

/-- The Fréchet derivative of the "componentwise quotient" map on the Pi model
`y ↦ fun i => y_i / y_{k+1}`, computed by `hasFDerivAt_pi` together with the product and
inverse rules. -/
lemma hasFDerivAt_divPi {k : ℕ} (y : Fin (k+1) → ℝ) (hy : y (Fin.last k) ≠ 0) :
    HasFDerivAt (fun y' : Fin (k+1) → ℝ => fun i : Fin k => y' (Fin.castSucc i) / y' (Fin.last k))
      (ContinuousLinearMap.pi (fun i : Fin k =>
        (-(y (Fin.castSucc i) * (y (Fin.last k)^2)⁻¹)) •
            (ContinuousLinearMap.proj (Fin.last k) : (Fin (k+1) → ℝ) →L[ℝ] ℝ)
          + (y (Fin.last k))⁻¹ •
            (ContinuousLinearMap.proj (Fin.castSucc i) : (Fin (k+1) → ℝ) →L[ℝ] ℝ))) y := by
  rw [hasFDerivAt_pi]
  intro i
  have h1 : HasFDerivAt (fun y' : Fin (k+1) → ℝ => y' (Fin.castSucc i))
      (ContinuousLinearMap.proj (Fin.castSucc i) : (Fin (k+1) → ℝ) →L[ℝ] ℝ) y :=
    ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj (Fin.castSucc i) : (Fin (k+1) → ℝ) →L[ℝ] ℝ)
  have h2 : HasFDerivAt (fun y' : Fin (k+1) → ℝ => (y' (Fin.last k))⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(y (Fin.last k)^2)⁻¹)) ∘SL
        (ContinuousLinearMap.proj (Fin.last k) : (Fin (k+1) → ℝ) →L[ℝ] ℝ)) y :=
    (hasFDerivAt_inv hy).comp y (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj (Fin.last k) : (Fin (k+1) → ℝ) →L[ℝ] ℝ))
  have h3 := h1.mul h2
  refine h3.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The `ContinuousLinearMap.pi` form of the derivative above coincides with
`(y_{k+1})⁻¹ • projAux u`, where `u_i = y_i/y_{k+1}`. -/
lemma pi_eq_smul_projAux {k : ℕ} (y : Fin (k+1) → ℝ) (hy : y (Fin.last k) ≠ 0) :
    ContinuousLinearMap.pi (fun i : Fin k =>
        (-(y (Fin.castSucc i) * (y (Fin.last k)^2)⁻¹)) •
            (ContinuousLinearMap.proj (Fin.last k) : (Fin (k+1) → ℝ) →L[ℝ] ℝ)
          + (y (Fin.last k))⁻¹ •
            (ContinuousLinearMap.proj (Fin.castSucc i) : (Fin (k+1) → ℝ) →L[ℝ] ℝ))
      = (y (Fin.last k))⁻¹ • projAux (fun i : Fin k => y (Fin.castSucc i) / y (Fin.last k)) := by
  ext w i
  rw [ContinuousLinearMap.pi_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, Pi.smul_apply, projAux_apply]
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- Derivative of the componentwise quotient map, phrased directly in terms of `projAux`. -/
lemma hasFDerivAt_divPi' {k : ℕ} (y : Fin (k+1) → ℝ) (hy : y (Fin.last k) ≠ 0) :
    HasFDerivAt (fun y' : Fin (k+1) → ℝ => fun i : Fin k => y' (Fin.castSucc i) / y' (Fin.last k))
      ((y (Fin.last k))⁻¹ • projAux (fun i : Fin k => y (Fin.castSucc i) / y (Fin.last k))) y :=
  (hasFDerivAt_divPi y hy).congr_fderiv (pi_eq_smul_projAux y hy)

/-- **The derivative of the extraction map** (`Work.Projection.extract` and `Work.Projection.projVec`
are defined in `Submission.Work.Projection.Basic`).  On the open set where the last coordinate does
not vanish, `extract` is smooth with derivative `z ↦ (z_last)⁻¹ • projVec (extract z)`.  Here
`extract z = (z_1/z_{k+1}, …, z_k/z_{k+1}) : ℝ^k` and `projVec u : ℝ^{k+1} →L[ℝ] ℝ^k` is the
projection with kernel spanned by `(u,1)`. -/
theorem hasFDerivAt_extract {k : ℕ} (z : EuclideanSpace ℝ (Fin (k + 1)))
    (hz : z (Fin.last k) ≠ 0) :
    HasFDerivAt (extract (k := k)) ((z (Fin.last k))⁻¹ • projVec (extract z)) z := by
  let e1 : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] (Fin (k+1) → ℝ) := EuclideanSpace.equiv (Fin (k+1)) ℝ
  let e0 : (Fin k → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin k) := (EuclideanSpace.equiv (Fin k) ℝ).symm
  let F : (Fin (k+1) → ℝ) → (Fin k → ℝ) := fun y i => y (Fin.castSucc i) / y (Fin.last k)
  have hy : (e1 z) (Fin.last k) ≠ 0 := by simpa [e1] using hz
  have hF : HasFDerivAt F
      (((e1 z) (Fin.last k))⁻¹ •
        projAux (fun i : Fin k => (e1 z) (Fin.castSucc i) / (e1 z) (Fin.last k))) (e1 z) :=
    hasFDerivAt_divPi' (e1 z) hy
  have h1 := hF.comp z (ContinuousLinearEquiv.hasFDerivAt e1 (x := z))
  have h2 := (ContinuousLinearEquiv.hasFDerivAt e0 (x := F (e1 z))).comp z h1
  refine h2.congr_fderiv ?_
  simp only [e1, e0, F, projVec, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_mk, ContinuousLinearMap.coe_comp,
    Function.comp_apply]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rfl

end Work.Projection
