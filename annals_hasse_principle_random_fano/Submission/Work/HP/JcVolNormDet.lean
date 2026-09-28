/-
# `Work.HP.JcVolNormDet`

For linearly independent `w z` in a Euclidean space `E = EuclideanSpace ℝ ι` the norm
determinant of the pairing map

`lamP w z : P = ℝw ⊕ ℝz → ℝ²,  a ↦ (⟪w,a⟫, ⟪z,a⟫)`

equals `√(deltaV w z)`, where `deltaV w z = ‖w‖²‖z‖² - ⟪w,z⟫²` is the Gram determinant
of the pair `(w,z)`.

The proof is a volume computation.  Let `psiP w z : ℝ² → P` be the coordinate map
`x ↦ x₀ • w + x₁ • z` (`Submission.Work.HP.JcVolNormDetDefs`).  With respect to the
standard orthonormal basis of `ℝ²` the composite `lamP w z ∘ psiP w z` is *exactly* the
Gram matrix

`gramG w z = !![‖w‖², ⟪w,z⟫; ⟪w,z⟫, ‖z‖²]`,

whose determinant is `deltaV w z`; hence `(lamP w z ∘ psiP w z).normDet = deltaV w z`.
On the other hand the images of the standard orthonormal basis of `ℝ²` under `psiP w z`
are `w` and `z`, so `normDet (psiP w z)² = det (gramG w z) = deltaV w z`, i.e.
`normDet (psiP w z) = √(deltaV w z)`.  Finally `normDet` is multiplicative on composites
of maps between spaces of equal dimension, so

`normDet (lamP w z) * √(deltaV w z) = normDet (lamP w z ∘ psiP w z) = deltaV w z`,

whence `normDet (lamP w z) = √(deltaV w z)`.
-/
import Mathlib
import Submission.Work.HP.JcVolDefs
import Submission.Work.HP.JcVolAlg
import Submission.Work.HP.JcVolNormDetDefs

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP

variable {ι : Type*} [Fintype ι]

/-- The matrix of `lamP w z ∘ₗ psiP w z` with respect to the standard orthonormal basis of
`ℝ²` is the Gram matrix of `(w,z)`. -/
lemma JcND_toMatrix_comp (w z : EuclideanSpace ℝ ι) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (lamP w z ∘ₗ psiP w z) = gramG w z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, gramG, real_inner_comm]

/-- The determinant of `lamP w z ∘ₗ psiP w z` is `deltaV w z`. -/
lemma JcND_comp_det (w z : EuclideanSpace ℝ ι) :
    (lamP w z ∘ₗ psiP w z).det = deltaV w z := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (lamP w z ∘ₗ psiP w z), JcND_toMatrix_comp w z, gramG_det]

/-- The norm determinant of `lamP w z ∘ₗ psiP w z` is `deltaV w z`. -/
lemma JcND_comp_normDet {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) :
    (lamP w z ∘ₗ psiP w z).normDet = deltaV w z := by
  rw [LinearMap.normDet_eq_abs_det, JcND_comp_det w z, abs_of_pos (JcVolDelta h)]

/-- The norm determinant of the coordinate map `psiP w z : ℝ² → P` is `√(deltaV w z)`. -/
lemma JcND_psiP_normDet (w z : EuclideanSpace ℝ ι) :
    (psiP w z).normDet = Real.sqrt (deltaV w z) := by
  have hgram : Matrix.gram ℝ
      (fun i : Fin 2 => psiP w z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = gramG w z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.gram_apply, Submodule.coe_inner, gramG, real_inner_comm]
  have hsq := LinearMap.normDet_sq_eq_det_gram (psiP w z) (EuclideanSpace.basisFun (Fin 2) ℝ)
  rw [hgram, gramG_det] at hsq
  have hsq' : (psiP w z).normDet ^ 2 = deltaV w z := by simpa using hsq
  have hnn : 0 ≤ (psiP w z).normDet := (psiP w z).normDet_nonneg
  calc (psiP w z).normDet = Real.sqrt ((psiP w z).normDet ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]
      _ = Real.sqrt (deltaV w z) := by rw [hsq']

/-- The plane `P = ℝw ⊕ ℝz` spanned by linearly independent vectors is two-dimensional. -/
lemma JcND_finrank_planeP {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) :
    Module.finrank ℝ ↥(planeP w z) = 2 := by
  have h1 := finrank_span_eq_card h
  rw [Fintype.card_fin] at h1
  have hsp : Submodule.span ℝ (Set.range ![w, z]) = planeP w z := by
    rw [planeP]
    congr 1
    ext x
    simp
    tauto
  rw [← hsp]
  exact h1

theorem JcVolNormDet {ι : Type*} [Fintype ι] {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) :
    (lamP w z).normDet = Real.sqrt (deltaV w z) := by
  have hδ : 0 < deltaV w z := JcVolDelta h
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = Module.finrank ℝ ↥(planeP w z) := by
    rw [finrank_euclideanSpace, JcND_finrank_planeP h]
    simp
  have hcomp := LinearMap.normDet_comp_of_finrank_eq (psiP w z) (lamP w z) hfin
  have h1 : (lamP w z).normDet * (psiP w z).normDet = deltaV w z := by
    rw [← hcomp, JcND_comp_normDet h]
  rw [JcND_psiP_normDet w z] at h1
  have key : (lamP w z).normDet * Real.sqrt (deltaV w z) =
      Real.sqrt (deltaV w z) * Real.sqrt (deltaV w z) := by
    rw [h1, ← pow_two, Real.sq_sqrt hδ.le]
  exact mul_right_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hδ)) key

end Work.HP
