import Mathlib
import Submission.Work.Bordism.interForm_pullback
import Submission.Work.SignatureBordism.Rationalisation

set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism

open CategoryTheory AlgebraicTopology
open scoped TensorProduct

noncomputable section

theorem sigmaHomeomorph {k : ℕ} (X Y : TopCat) (e : X ≅ Y)
    (c : (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homology (k + k)) :
    Work.SignatureBordism.sigma k (TopCat.toSSet.obj Y)
        (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y e.hom) (k + k) c)
      = Work.SignatureBordism.sigma k (TopCat.toSSet.obj X) c := by
  haveI : CategoryTheory.IsIso (Work.Cohomology.singularCohomologyMap ℤ X Y e.hom k) := by
    refine CategoryTheory.IsIso.mk ⟨Work.Cohomology.singularCohomologyMap ℤ Y X e.inv k, ?_, ?_⟩
    · rw [← Work.Cohomology.singularCohomologyMap_comp, e.inv_hom_id,
        Work.Cohomology.singularCohomologyMap_id]
    · rw [← Work.Cohomology.singularCohomologyMap_comp, e.hom_inv_id,
        Work.Cohomology.singularCohomologyMap_id]
  let ψ : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj Y)).homology k ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homology k :=
    (CategoryTheory.asIso (Work.Cohomology.singularCohomologyMap ℤ X Y e.hom k)).toLinearEquiv
  have hψ : ∀ y, ψ y = Work.Cohomology.singularCohomologyMap ℤ X Y e.hom k y := fun y => rfl
  let T : (ℚ ⊗[ℤ] (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj Y)).homology k) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homology k) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ) ψ
  have hT : ∀ (a : ℚ) (y : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj Y)).homology k),
      T (a ⊗ₜ[ℤ] y) = a ⊗ₜ[ℤ] ψ y := by
    intro a y
    rw [TensorProduct.AlgebraTensorModule.congr_tmul]
    rfl
  let Bx := Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj X) c
  let By := Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj Y)
    (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y e.hom) (k + k) c)
  let C : (ℚ ⊗[ℤ] (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj Y)).homology k) →ₗ[ℚ]
      (ℚ ⊗[ℤ] (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj Y)).homology k) →ₗ[ℚ] ℚ :=
    (Bx.comp (T : _ →ₗ[ℚ] _)).compl₂ (T : _ →ₗ[ℚ] _)
  have hnat : ∀ y z : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj Y)).homology k,
      Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj X) k k c (ψ y) (ψ z)
        = Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj Y) k k
            (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y e.hom) (k + k) c)
            y z := by
    intro y z
    rw [hψ y, hψ z]
    exact Work.Bordism.interForm_pullback e.hom k c y z
  have hval : ∀ (a b : ℚ) (y z : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj Y)).homology k),
      C (a ⊗ₜ[ℤ] y) (b ⊗ₜ[ℤ] z)
        = (a * b) * (Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj X) k k c (ψ y)
            (ψ z) : ℚ) := by
    intro a b y z
    show Bx (T (a ⊗ₜ[ℤ] y)) (T (b ⊗ₜ[ℤ] z)) = _
    rw [hT a y, hT b z]
    exact Work.SignatureBordism.ratInterForm_tmul k (TopCat.toSSet.obj X) c a b (ψ y) (ψ z)
  have hC : By = C := by
    refine Work.SignatureBordism.tensor_bilin_ext (fun a b y z => ?_)
    show Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj Y)
        (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y e.hom) (k + k) c)
          (a ⊗ₜ[ℤ] y) (b ⊗ₜ[ℤ] z) = C (a ⊗ₜ[ℤ] y) (b ⊗ₜ[ℤ] z)
    rw [Work.SignatureBordism.ratInterForm_tmul]
    rw [hval]
    rw [hnat]
  have hquad : Work.SignatureBordism.quadOfBilin By
      = (Work.SignatureBordism.quadOfBilin Bx).comp (T : _ →ₗ[ℚ] _) := by
    rw [hC]
    apply QuadraticMap.ext
    intro y
    simp only [QuadraticMap.comp_apply, Work.SignatureBordism.quadOfBilin_apply]
    rfl
  show Work.SignatureBordism.signature (Work.SignatureBordism.quadOfBilin By)
      = Work.SignatureBordism.signature (Work.SignatureBordism.quadOfBilin Bx)
  rw [hquad]
  exact Work.SignatureBordism.signature_comp_linearEquiv (Work.SignatureBordism.quadOfBilin Bx) T

end

end Work.ThomBordism
