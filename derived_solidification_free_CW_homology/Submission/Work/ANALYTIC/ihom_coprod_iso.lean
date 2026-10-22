import Mathlib
import Submission.Work.ANALYTIC.Basic

/-!
# Internal hom out of a coproduct in light condensed abelian groups

For a family `A : J → LightCondAb` and an object `Z : LightCondAb`,

  `[∐_j A_j, Z] ≅ ∏_j [A_j, Z]`

where `[X, Z] = (ihom X).obj Z` is the internal hom.

In any monoidal closed category this holds because `tensorLeft W` is a left adjoint, hence
preserves the coproduct, so that for every `W` there is a natural bijection

  `Hom(W ⊗ ∐_j A_j, Z) ≅ ∏_j Hom(W ⊗ A_j, Z)`.

Formally, we use the parametrized adjunction `curriedTensor C ⊣₂ internalHom`
(`MonoidalClosed.internalHomAdjunction₂`): its right adjoint `internalHom.flip.obj Z` is the
functor `Cᵒᵖ ⥤ C`, `X ↦ [X, Z]`, which — in a braided monoidal closed category — preserves all
limits (`ParametrizedAdjunction.preservesLimitsOfShape_flip_obj`, available for
`MonoidalClosed.internalHom.flip.obj Z` via the instance in
`Mathlib.CategoryTheory.Monoidal.Closed.Braided`).  A coproduct cocone in `C` is a limit
cone in `Cᵒᵖ` (`Cocone.op`), so `[∐_j A_j, Z]` is the limit of the diagram `j ↦ [A_j, Z]`, i.e. the
product.
-/

open CategoryTheory MonoidalCategory Limits

namespace Work.ANALYTIC

set_option maxHeartbeats 1600000 in
theorem ihom_coprod_iso (J : Type) (A : J → LightCondAb) (Z : LightCondAb)
    [CategoryTheory.Limits.HasCoproduct A]
    [CategoryTheory.Limits.HasProduct (fun j : J => (CategoryTheory.ihom (A j)).obj Z)] :
    Nonempty (CategoryTheory.Iso ((CategoryTheory.ihom (CategoryTheory.Limits.sigmaObj A)).obj Z)
      (CategoryTheory.Limits.piObj (fun j : J => (CategoryTheory.ihom (A j)).obj Z))) := by
  classical
  let f : J → LightCondAb := fun j => (ihom (A j)).obj Z
  -- `[-, Z]` as a functor `Cᵒᵖ ⥤ C`, the right adjoint of `curriedTensor C`
  let G : LightCondAbᵒᵖ ⥤ LightCondAb := MonoidalClosed.internalHom.flip.obj Z
  -- the coproduct cocone of the family `A`
  let c : Cofan A := Cofan.mk (sigmaObj A) (Sigma.ι A)
  have hc : IsColimit c := coproductIsCoproduct A
  -- a coproduct cocone in `C` is a limit cone in `Cᵒᵖ`, and `G` preserves such limits
  have hlim0 : IsLimit (G.mapCone (Cocone.op c)) := isLimitOfPreserves G (IsColimit.op hc)
  -- reindex the limit along the equivalence `Discrete J ≌ (Discrete J)ᵒᵖ`
  have hlim1 : IsLimit (Cone.whisker (Discrete.opposite J).symm.functor (G.mapCone (Cocone.op c))) :=
    hlim0.whiskerEquivalence (Discrete.opposite J).symm
  -- the reindexed diagram is the discrete diagram of the objects `[A_j, Z]`
  have hD : (Discrete.opposite J).symm.functor ⋙ ((Discrete.functor A).op ⋙ G) =
      Discrete.functor f := by
    apply Discrete.functor_ext
    intro j
    rfl
  have α : ((Discrete.opposite J).symm.functor ⋙ ((Discrete.functor A).op ⋙ G)) ≅
      Discrete.functor f := eqToIso hD
  have hlim2 : IsLimit ((Cone.postcompose α.hom).obj
      (Cone.whisker (Discrete.opposite J).symm.functor (G.mapCone (Cocone.op c)))) :=
    (IsLimit.postcomposeHomEquiv α _).symm hlim1
  -- the product cone of the `[A_j, Z]` is a limit of the same diagram
  exact ⟨hlim2.conePointUniqueUpToIso (productIsProduct f)⟩

end Work.ANALYTIC
