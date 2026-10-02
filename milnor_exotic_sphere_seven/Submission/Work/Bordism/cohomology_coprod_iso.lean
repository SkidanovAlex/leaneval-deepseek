import Mathlib
import Submission.Work.Bordism.chainC_coprod_iso
import Submission.Work.Bordism.dualComplex_biprod
import Submission.Work.Cohomology.homology_biprod_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cohomology of a disjoint union (Künneth for disjoint unions)

For topological spaces `X`, `Y` and every degree `k`, the singular cohomology of the coproduct
splits as the direct sum of the cohomologies of the two pieces:

`Hᵏ(X ⊔ Y;ℤ) ≅ Hᵏ(X;ℤ) ⊕ Hᵏ(Y;ℤ)`

(`Work.Bordism.cohomology_coprod_iso`).  This completes the "Künneth for disjoint unions" package of
this chapter: the coproduct of singular simplices (`Work.Bordism.toSSet_coprod_iso`,
`Work.Bordism.coprod_simplices_equiv`), of the singular chain complexes
(`Work.Bordism.chainC_coprod_iso`), of homology (`Work.Bordism.homology_coprod_iso`), of the
intersection form (`Work.Bordism.interForm_coprod`) and now of cohomology.

The proof dualises the chain-level splitting (`Work.Cohomology.dualComplex`,
`Work.Cohomology.dualComplexMap`, `Work.Bordism.dualComplex_biprod`) and applies the additivity of
homology over biproducts (`Work.Cohomology.homology_biprod_iso`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory Limits

namespace Work.Bordism

open Work.Cohomology

noncomputable section

/-- **Cohomology of a disjoint union**: `Hᵏ(X ⊔ Y;ℤ) ≅ Hᵏ(X;ℤ) ⊕ Hᵏ(Y;ℤ)`. -/
theorem cohomology_coprod_iso (X Y : TopCat) (k : ℕ) :
    Nonempty (HomologicalComplex.homology
        (cochainC ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod X Y))) k ≅
      (HomologicalComplex.homology (cochainC ℤ (TopCat.toSSet.obj X)) k ⊞
        HomologicalComplex.homology (cochainC ℤ (TopCat.toSSet.obj Y)) k)) := by
  obtain ⟨e⟩ := chainC_coprod_iso X Y
  obtain ⟨d⟩ := dualComplex_biprod (chainC ℤ (TopCat.toSSet.obj X))
    (chainC ℤ (TopCat.toSSet.obj Y))
  obtain ⟨h⟩ := homology_biprod_iso (dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj X)))
    (dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj Y))) k
  -- the dual of the chain-level splitting
  let eD : dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod X Y))) ≅
      dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj X) ⊞ chainC ℤ (TopCat.toSSet.obj Y)) :=
    { hom := dualComplexMap ℤ _ _ e.inv
      inv := dualComplexMap ℤ _ _ e.hom
      hom_inv_id := by
        rw [← dualComplexMap_comp, e.hom_inv_id, dualComplexMap_id]
      inv_hom_id := by
        rw [← dualComplexMap_comp, e.inv_hom_id, dualComplexMap_id] }
  exact ⟨((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) k).mapIso eD)
      ≪≫ ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) k).mapIso d)
      ≪≫ h⟩

end

end Work.Bordism
