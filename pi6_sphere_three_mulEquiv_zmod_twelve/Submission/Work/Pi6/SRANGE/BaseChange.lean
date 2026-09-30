import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Pi6.EMM2.finiteType
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Base change of the singular chain complex along `ℤ → R`

For every commutative ring `R` the singular chain complex of a simplicial set `X` with
coefficients in `R` is the base change along `ℤ → R` of the integral one:

`C_*(X; ℤ) ⊗[ℤ] R ≅ C_*(X; R)`.

This file proves the isomorphism `Work.Pi6.SRANGE.BaseChange`, *naturally* in `X` (i.e. the
isomorphisms commute with the maps induced by a morphism of simplicial sets).  The proof is
functorial: `C_*(X; R)` is obtained from `C_*(X; ℤ)` by applying the additive functor
`- ⊗[ℤ] R` to the levelwise coproduct of copies of the coefficients, using that a functor
preserving coproducts commutes with `sigmaConst` (`Work.StemsB.SphRat.sigmaConstObjCompIso`)
and that the alternating face map complex commutes with the application of an additive functor
(`AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped TensorProduct

namespace Work.Pi6.SRANGE

noncomputable section

variable (R : Type) [CommRing R]

/-- **Base change is natural in the simplicial set.**  The isomorphism
`C_*(X; ℤ) ⊗[ℤ] R ≅ C_*(X; R)` is induced by the functor `- ⊗[ℤ] R` and is therefore natural
in `X`. -/
noncomputable def baseChangeNatIso :
    ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj ZModZ)
        ⋙ ((IntR R).mapHomologicalComplex (ComplexShape.down ℕ))
      ≅ (SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (RMod R) := by
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S) (IntR R) := fun _ => inferInstance
  have h1 : (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj ZModZ
      = (SimplicialObject.whiskering (Type) (ModuleCat.{0} ℤ)).obj (sigmaConst.obj ZModZ)
          ⋙ alternatingFaceMapComplex (ModuleCat.{0} ℤ) := rfl
  have h2 : (SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (RMod R)
      = (SimplicialObject.whiskering (Type) (ModuleCat.{0} R)).obj (sigmaConst.obj (RMod R))
          ⋙ alternatingFaceMapComplex (ModuleCat.{0} R) := rfl
  rw [h1, h2]
  refine (Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (alternatingFaceMapComplexCompMapHomologicalComplexIso (IntR R)) ≪≫
    (Functor.associator _ _ _).symm ≪≫ ?_)
  exact Functor.isoWhiskerRight
    (eqToIso (Functor.whiskeringRight_obj_comp (sigmaConst.obj ZModZ) (IntR R)) ≪≫
      (SimplicialObject.whiskering (Type) (ModuleCat.{0} R)).mapIso
        (Work.StemsB.SphRat.sigmaConstObjCompIso (IntR R) ZModZ ≪≫
          sigmaConst.mapIso (Work.Pi6.EMM2.extendScalarsSelfIso (Int.castRingHom R))))
    (alternatingFaceMapComplex (ModuleCat.{0} R))

end

theorem BaseChange (R : Type) [CommRing R] : ∃ e : (forall X : SSet.{0}, Work.Pi6.SRANGE.baseChange R (SSet.chainComplex X Work.Pi6.SRANGE.ZModZ) ≅ SSet.chainComplex X (Work.Pi6.SRANGE.RMod R)), (forall (X Y : SSet.{0}) (sigma : X ⟶ Y), CategoryTheory.CategoryStruct.comp (e X).hom (SSet.chainComplexMap sigma (Work.Pi6.SRANGE.RMod R)) = CategoryTheory.CategoryStruct.comp (Work.Pi6.SRANGE.baseChangeMap R (SSet.chainComplexMap sigma Work.Pi6.SRANGE.ZModZ)) (e Y).hom) := by
  refine ⟨fun X => (baseChangeNatIso R).app X, ?_⟩
  intro X Y sigma
  have h := (baseChangeNatIso R).hom.naturality sigma
  rw [Functor.comp_map] at h
  exact h.symm

end Work.Pi6.SRANGE
