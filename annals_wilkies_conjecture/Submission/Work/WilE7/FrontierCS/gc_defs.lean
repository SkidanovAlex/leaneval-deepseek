/-
  WilE7 / CS-slice, node N5 (`grid_cover`): auxiliary definitions and matrix/CLM glue.

  Node N5 passes between two languages:

  * the linear-algebraic grid lemma `exists_grid_det_ne_zero`, which is stated in terms of
    0/1 matrices and determinants;
  * the calculus of the slice charts `sliceChart γ B Λ`, whose derivative conditions live in
    `ContinuousLinearMap` land.

  This file collects the dictionary: `mat` (the matrix of a CLM between coordinate spaces),
  `matCLM` (the CLM of a matrix), and the derivative `sliceDeriv γ B t` of the chart
  `(t,e) ↦ γ t + B e` in the `t`-direction.
-/
import Mathlib
import Submission.Work.WilE7.FrontierCS.Defs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.FrontierCS

/-- The matrix of a continuous linear map `ℝ^n → ℝ^m`, in the standard bases. -/
noncomputable def mat {m n : ℕ} (f : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :
    Matrix (Fin m) (Fin n) ℝ :=
  LinearMap.toMatrix' (f : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))

/-- The continuous linear map `ℝ^n → ℝ^m` attached to a matrix. -/
noncomputable def matCLM {m n : ℕ} (Λ : Matrix (Fin m) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap Λ.mulVecLin

/-- The derivative of the chart `(t,e) ↦ γ t + B e` in the `t`-direction, i.e. of the chart
`(t,e) ↦ (γ t + B e)` viewed as a map `ℝ^d × ℝ^j → ℝ^N`. -/
noncomputable def sliceDeriv {N d j : ℕ} (γ : (Fin d → ℝ) → (Fin N → ℝ))
    (B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ)) (t : Fin d → ℝ) :
    ((Fin d → ℝ) × (Fin j → ℝ)) →L[ℝ] (Fin N → ℝ) :=
  (fderiv ℝ γ t).comp (ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin j → ℝ)) +
    B.comp (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin j → ℝ))

@[simp] lemma matCLM_apply {m n : ℕ} (Λ : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    matCLM Λ v = Λ.mulVec v :=
  rfl

@[simp] lemma sliceDeriv_apply {N d j : ℕ} (γ : (Fin d → ℝ) → (Fin N → ℝ))
    (B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ)) (t : Fin d → ℝ)
    (p : (Fin d → ℝ) × (Fin j → ℝ)) :
    sliceDeriv γ B t p = fderiv ℝ γ t p.1 + B p.2 :=
  rfl

@[simp] lemma mat_apply {m n : ℕ} (f : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) (i : Fin m)
    (j : Fin n) : mat f i j = f (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _

lemma mat_mulVec {m n : ℕ} (f : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) (v : Fin n → ℝ) :
    (mat f).mulVec v = f v :=
  LinearMap.toMatrix'_mulVec _ v

lemma mat_add {m n : ℕ} (f g : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :
    mat (f + g) = mat f + mat g := by
  ext i j
  simp [mat, LinearMap.toMatrix'_apply]

lemma mat_comp {l m n : ℕ} (f : (Fin m → ℝ) →L[ℝ] (Fin l → ℝ))
    (g : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) : mat (f.comp g) = mat f * mat g := by
  have h : (LinearMap.toMatrix' ((f.comp g : (Fin n → ℝ) →L[ℝ] (Fin l → ℝ)) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin l → ℝ))) =
      LinearMap.toMatrix' ((f : (Fin m → ℝ) →ₗ[ℝ] (Fin l → ℝ)).comp
        (g : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))) := rfl
  simp only [mat]
  rw [h, LinearMap.toMatrix'_comp]

lemma mat_matCLM {m n : ℕ} (Λ : Matrix (Fin m) (Fin n) ℝ) : mat (matCLM Λ) = Λ := by
  ext i j
  simp [mat, matCLM, LinearMap.toMatrix'_apply]

/-- The matrix of `F ∘ (A ∘ Λ + B)`, the shape in which the grid lemma is applied: the
`Λ`-column-contribution and the `B`-column-contribution add up. -/
lemma mat_comp_add_matCLM {j N d : ℕ} (F : (Fin N → ℝ) →L[ℝ] (Fin j → ℝ))
    (A : (Fin d → ℝ) →L[ℝ] (Fin N → ℝ)) (B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ))
    (Λ : Matrix (Fin d) (Fin j) ℝ) :
    mat (F.comp (A.comp (matCLM Λ) + B)) = mat F * mat A * Λ + mat F * mat B := by
  rw [mat_comp, mat_add, mat_comp, mat_matCLM, Matrix.mul_add, Matrix.mul_assoc]

/-- A square CLM whose matrix has nonzero determinant is surjective. -/
lemma range_top_of_mat_det_ne_zero {j : ℕ} (S : (Fin j → ℝ) →L[ℝ] (Fin j → ℝ))
    (h : (mat S).det ≠ 0) : S.range = ⊤ := by
  have hU : IsUnit (mat S) :=
    (Matrix.isUnit_iff_isUnit_det (mat S)).mpr (isUnit_iff_ne_zero.mpr h)
  have hsurj : Function.Surjective (mat S).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hU
  rw [LinearMap.range_eq_top]
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨x, ?_⟩
  rw [mat_mulVec] at hx
  exact hx

end Work.WilE7.FrontierCS
