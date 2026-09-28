import Mathlib
import Submission.Work.Kunneth.EZAWTensor
import Submission.Work.Kunneth.Algebra
import Submission.Work.Kunneth.exists_splitting
import Submission.Work.Kunneth.tpMap_homotopy

/-!
# Tensoring with a splitting: `Hₙ(C ⊗ D) ≅ Hₙ(C ⊗ homSum D)`

`Work.Kunneth.exists_splitting` produces, for a chain complex `D` of `ℤ`-modules whose terms and
homology are projective (free), a chain map `π : D ⟶ homSum D` and a chain map `ι : homSum D ⟶ D`
with `ι ≫ π = 𝟙` and `π ≫ ι ≃ 𝟙`.  Since `tpC C ·` is a functor (`Work.Kunneth.tpMap`,
`tpMap_comp`, `tpMap_id`) which carries homotopies to homotopies (`Work.Kunneth.tpMap_homotopy`),
tensoring with any `C` gives a homotopy equivalence `tpC C D ≃ tpC C (homSum D)`, and hence an
isomorphism on homology in every degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **Tensoring with a splitting**: if `D` has projective terms and projective homology, then the
tensor product of any complex `C` with `D` has the same homology as its tensor product with
`homSum D`. -/
theorem homology_tpC_homSum (C D : ChainComplex (ModuleCat ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    Nonempty (CategoryTheory.Iso ((Work.Kunneth.tpC C D).homology n)
      ((Work.Kunneth.tpC C (Work.Kunneth.homSum D)).homology n)) := by
  obtain ⟨π, ι, h₁, h₂⟩ := exists_splitting D hD hH
  obtain ⟨h₂'⟩ := h₂
  obtain ⟨hhom⟩ := tpMap_homotopy C C D D (𝟙 C) (𝟙 C)
    (CategoryTheory.CategoryStruct.comp π ι) (𝟙 D) (Homotopy.refl _) h₂'
  refine ⟨CategoryTheory.Iso.mk
    (HomologicalComplex.homologyMap (tpMap C C D (homSum D) (𝟙 C) π) n)
    (HomologicalComplex.homologyMap (tpMap C C (homSum D) D (𝟙 C) ι) n) ?_ ?_⟩
  · have hid : CategoryTheory.CategoryStruct.comp (𝟙 C) (𝟙 C) = 𝟙 C :=
      CategoryTheory.Category.id_comp (𝟙 C)
    rw [← HomologicalComplex.homologyMap_comp, tpMap_comp, hid,
      Homotopy.homologyMap_eq hhom n, tpMap_id, HomologicalComplex.homologyMap_id]
  · have hid : CategoryTheory.CategoryStruct.comp (𝟙 C) (𝟙 C) = 𝟙 C :=
      CategoryTheory.Category.id_comp (𝟙 C)
    rw [← HomologicalComplex.homologyMap_comp, tpMap_comp, hid, h₁, tpMap_id,
      HomologicalComplex.homologyMap_id]

end

end Work.Kunneth
