import Mathlib

open CategoryTheory

namespace Work.ANALYTIC.CechPt

theorem afmc_whisker_iso {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] [CategoryTheory.Preadditive C] [CategoryTheory.Preadditive D]
    (F : CategoryTheory.Functor C D) [F.Additive] (S : CategoryTheory.SimplicialObject C) :
    Nonempty (CategoryTheory.Iso
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (CategoryTheory.Functor.comp S F))
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj S))) := by
  -- Both complexes have the same objects in each degree, and the differentials
  -- agree because an additive functor commutes with the alternating sum of faces.
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) ?_⟩
  intro i j hij
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  rw [Functor.mapHomologicalComplex_obj_d]
  rw [ComplexShape.down_Rel] at hij
  subst hij
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
      AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Functor.map_sum]
  simp only [Functor.map_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  congr 1

end Work.ANALYTIC.CechPt
