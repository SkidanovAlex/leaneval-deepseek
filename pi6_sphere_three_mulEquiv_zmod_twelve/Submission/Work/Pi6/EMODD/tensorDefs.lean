import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.SRANGE.Defs
import Submission.Work.Pi6.K2Z.baseChangeFlat
import Submission.Work.StemsB.sphRatHomology
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Naturality of the base change `ℤ → 𝕜` of the singular chain complex

For a commutative ring `𝕜` the comparison `C_*(X;ℤ) ⊗[ℤ] 𝕜 ≅ C_*(X;𝕜)` of the singular chain
complexes of a simplicial set is natural in `X`: this is `Work.Pi6.EMODD.baseChangeNat`.

The comparison is assembled, exactly as in `Submission/Work/Pi6/SRANGE/BaseChange.lean` from

* the isomorphism of chain-complex functors `map_alternatingFaceMapComplex`, and
* `sigmaConstObjCompIso` (a functor preserving coproducts commutes with `sigmaConst`),

together with the coefficient isomorphism `𝕜 ⊗[ℤ] ℤ ≅ 𝕜`
(`Work.Pi6.K2Z.extendScalarsIntFieldIso`).  Because the comparison is built as an isomorphism
between *functors* (from `SSet` to chain complexes over `𝕜`) its naturality is automatic.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped TensorProduct

namespace Work.Pi6.EMODD

noncomputable section

/-- **Base change is natural in the simplicial set.**  The isomorphism
`C_*(X;ℤ) ⊗[ℤ] 𝕜 ≅ C_*(X;𝕜)` induced by the functor `- ⊗[ℤ] 𝕜` is natural in `X`. -/
noncomputable def baseChangeNatIso (𝕜 : Type) [CommRing 𝕜] :
    ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj Work.Pi6.SRANGE.ZModZ)
        ⋙ ((Work.Pi6.SRANGE.IntR 𝕜).mapHomologicalComplex (ComplexShape.down ℕ))
      ≅ (SSet.chainComplexFunctor (ModuleCat.{0} 𝕜)).obj (Work.Pi6.SRANGE.RMod 𝕜) := by
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S) (Work.Pi6.SRANGE.IntR 𝕜) :=
    fun _ => inferInstance
  have h1 : (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj Work.Pi6.SRANGE.ZModZ
      = (SimplicialObject.whiskering (Type) (ModuleCat.{0} ℤ)).obj
          (sigmaConst.obj Work.Pi6.SRANGE.ZModZ)
          ⋙ alternatingFaceMapComplex (ModuleCat.{0} ℤ) := rfl
  have h2 : (SSet.chainComplexFunctor (ModuleCat.{0} 𝕜)).obj (Work.Pi6.SRANGE.RMod 𝕜)
      = (SimplicialObject.whiskering (Type) (ModuleCat.{0} 𝕜)).obj
          (sigmaConst.obj (Work.Pi6.SRANGE.RMod 𝕜))
          ⋙ alternatingFaceMapComplex (ModuleCat.{0} 𝕜) := rfl
  rw [h1, h2]
  refine (Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (alternatingFaceMapComplexCompMapHomologicalComplexIso
      (Work.Pi6.SRANGE.IntR 𝕜)) ≪≫
    (Functor.associator _ _ _).symm ≪≫ ?_)
  exact Functor.isoWhiskerRight
    (eqToIso (Functor.whiskeringRight_obj_comp (sigmaConst.obj Work.Pi6.SRANGE.ZModZ)
        (Work.Pi6.SRANGE.IntR 𝕜)) ≪≫
      (SimplicialObject.whiskering (Type) (ModuleCat.{0} 𝕜)).mapIso
        (Work.StemsB.SphRat.sigmaConstObjCompIso (Work.Pi6.SRANGE.IntR 𝕜)
          Work.Pi6.SRANGE.ZModZ ≪≫
          sigmaConst.mapIso (Work.Pi6.K2Z.extendScalarsIntFieldIso 𝕜)))
    (alternatingFaceMapComplex (ModuleCat.{0} 𝕜))

/-- **Naturality of the base change in the simplicial set.** -/
theorem baseChangeNat (𝕜 : Type) [CommRing 𝕜] :
    ∃ e : (∀ X : SSet.{0},
      Work.Pi6.SRANGE.baseChange 𝕜 (SSet.chainComplex X Work.Pi6.SRANGE.ZModZ)
        ≅ SSet.chainComplex X (Work.Pi6.SRANGE.RMod 𝕜)),
      (∀ (X Y : SSet.{0}) (sigma : X ⟶ Y),
        CategoryTheory.CategoryStruct.comp (e X).hom
            (SSet.chainComplexMap sigma (Work.Pi6.SRANGE.RMod 𝕜))
          = CategoryTheory.CategoryStruct.comp
              (Work.Pi6.SRANGE.baseChangeMap 𝕜
                (SSet.chainComplexMap sigma Work.Pi6.SRANGE.ZModZ)) (e Y).hom) := by
  refine ⟨fun X => (baseChangeNatIso 𝕜).app X, ?_⟩
  intro X Y sigma
  have h := (baseChangeNatIso 𝕜).hom.naturality sigma
  rw [Functor.comp_map] at h
  exact h.symm

end

end Work.Pi6.EMODD
