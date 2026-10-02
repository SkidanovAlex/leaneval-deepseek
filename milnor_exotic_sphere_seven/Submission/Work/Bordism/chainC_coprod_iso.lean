import Mathlib
import Submission.Work.Cohomology.exists_capH
import Submission.Work.Bordism.toSSet_coprod_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `chainC ℤ` sends a coproduct of simplicial sets to the biproduct of chain complexes

This file proves `Work.Bordism.chainC_coprod_iso`, the Künneth-type splitting which says that the
singular chain complex (with `ℤ`-coefficients, as packaged by `Work.Cohomology.chainC`) of a
disjoint union `X ⊔ Y` of topological spaces is the biproduct of the chain complexes of the pieces.

The proof has two halves.

* `chainC_preservesColimitsOfShape` : the functor `chainC ℤ : SSet ⥤ ChainComplex (ModuleCat ℤ) ℕ`
  preserves all colimits.  Indeed it is the composite
  `(sigmaConst ⋙ SimplicialObject.whiskering Type (ModuleCat ℤ)).obj ℤ ⋙ alternatingFaceMapComplex`
  of a postcomposition with a colimit preserving functor (`sigmaConst.obj R` preserves colimits) and
  of the alternating face map complex, whose composite with each evaluation `HomologicalComplex.eval`
  is an evaluation functor, hence colimit preserving
  (`HomologicalComplex.preservesColimitsOfShape_of_eval`).

* `chainC_coprod_iso_sset` : consequently `chainC ℤ` carries the coproduct `A ⨿ B` of simplicial
  sets to `colimit (pair A B ⋙ chainC ℤ)`, and in the additive category of chain complexes this is
  the biproduct `chainC ℤ A ⊞ chainC ℤ B`.

The remaining input, supplied by `Work.Bordism.toSSet_coprod_iso`, is that the singular simplicial
set of a disjoint union of topological spaces is the coproduct of the singular simplicial sets: the
standard simplex is connected, so every singular simplex of `X ⊔ Y` lands in one piece.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits HomologicalComplex
open scoped Simplicial

namespace Work.Bordism

noncomputable section

section PreservesColimits

variable (J : Type) [Category J] [HasColimitsOfShape J (ModuleCat ℤ)]

/-- The functor `chainC ℤ` preserves `J`-shaped colimits. -/
theorem chainC_preservesColimitsOfShape :
    PreservesColimitsOfShape J
      ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)) := by
  let R : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
  let S : SSet ⥤ SimplicialObject (ModuleCat.{0} ℤ) :=
    (sigmaConst ⋙ SimplicialObject.whiskering Type (ModuleCat.{0} ℤ)).obj R
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro i
  haveI h3 : PreservesColimitsOfShape J
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{0} ℤ) ⋙
        HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) i) :=
    show PreservesColimitsOfShape J
      ((evaluation (SimplexCategoryᵒᵖ) (ModuleCat.{0} ℤ)).obj
        (Opposite.op (SimplexCategory.mk i))) from inferInstance
  haveI h1 : PreservesColimitsOfShape J S :=
    show PreservesColimitsOfShape J
      ((Functor.whiskeringRight (SimplexCategoryᵒᵖ) Type (ModuleCat.{0} ℤ)).obj
        (sigmaConst.obj R)) from inferInstance
  show PreservesColimitsOfShape J
    (S ⋙ (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{0} ℤ) ⋙
        HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) i))
  refine ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩
  obtain ⟨hc1⟩ := (h1.preservesColimit (K := K)).preserves hc
  obtain ⟨hc2⟩ := (h3.preservesColimit (K := K ⋙ S)).preserves hc1
  exact ⟨hc2⟩

end PreservesColimits

/-- `chainC ℤ` carries a coproduct of simplicial sets to the biproduct of the chain complexes. -/
theorem chainC_coprod_iso_sset (A B : SSet) :
    Nonempty (Work.Cohomology.chainC ℤ (A ⨿ B) ≅
      Work.Cohomology.chainC ℤ A ⊞ Work.Cohomology.chainC ℤ B) := by
  let G : SSet ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
    (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)
  haveI hpres : PreservesColimit (pair A B) G :=
    (chainC_preservesColimitsOfShape (J := Discrete WalkingPair)).preservesColimit
  let e1 := preservesColimitIso G (pair A B)
  let e2 := HasColimit.isoOfNatIso (diagramIsoPair ((pair A B) ⋙ G))
  let e3 := (IsColimit.coconePointUniqueUpToIso
    (BinaryBiproduct.isColimit (G.obj A) (G.obj B))
    (colimit.isColimit (pair (G.obj A) (G.obj B)))).symm
  exact ⟨e1 ≪≫ e2 ≪≫ e3⟩

/-- The singular chain complex (with `ℤ`-coefficients) of a disjoint union of topological spaces
is the biproduct of the chain complexes of the pieces. -/
theorem chainC_coprod_iso (X Y : TopCat) :
    Nonempty (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod X Y)) ≅
      (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X) ⊞
        Work.Cohomology.chainC ℤ (TopCat.toSSet.obj Y))) := by
  obtain ⟨e⟩ := toSSet_coprod_iso X Y
  obtain ⟨e'⟩ := chainC_coprod_iso_sset (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
  exact ⟨Functor.mapIso
    ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)) e ≪≫ e'⟩

end

end Work.Bordism
