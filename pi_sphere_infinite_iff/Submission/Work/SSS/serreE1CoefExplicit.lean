import Mathlib
import Submission.Work.SSS.serreE1CoefIso
import Submission.Work.SSS.tensorComplexIsoExpTens
import Submission.Work.SSS.normalizedCoeffIso
import Submission.Work.SSS.HomologySigmaAux
import Submission.Work.SSS.coprodComplex_iso

/-!
# Explicit (transparent) forms of the coefficient isomorphisms

The statements `serreE1CoefIso`, `normalizedCoeffIso`, `tensorComplexIsoExpTens` and
`coprodComplex_iso` are `Nonempty`-valued: the isomorphisms they assert exist are produced by
`Classical.choice`, hence opaque, and no statement about their behaviour can be derived from their
types.  For the identification of the differential `d¹` of the E¹ page with `∂ ⊗ id` we need the
*specific* isomorphisms; this file re-exposes them as `def`s (the constructions are the ones
already used inside the proofs of those statements).
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped MonoidalCategory

noncomputable section

/-- **Explicit form of `Work.SSS.tensorComplexIsoExpTens`.**  The tensor complex `K ⊗ M` is the
naive coefficient extension `expTens K M`, via the inverse of the explicit chain isomorphism
`split K M` (whose inverse is supplied degreewise by `collapseX`). -/
noncomputable def tensorComplexIsoExpTensIso (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) :
    Work.SSS.tensorComplex K M ≅ Work.SSS.expTens K M := by
  haveI : ∀ n, IsIso ((split K M).f n) := fun n =>
    ⟨collapseX K M n, splitX_collapseX K M n, collapseX_splitX K M n⟩
  haveI : IsIso (split K M) := HomologicalComplex.Hom.isIso_of_components _
  exact (asIso (split K M)).symm

/-- **Explicit form of `Work.SSS.sigmaConstTensorIso`.** -/
noncomputable def sigmaConstTensorIsoIso (M : ModuleCat ℤ) :
    (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ) ⋙ MonoidalCategory.tensorRight M :
        Type ⥤ ModuleCat ℤ) ≅
      (Limits.sigmaConst.obj M : Type ⥤ ModuleCat ℤ) := by
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S) (MonoidalCategory.tensorRight M) :=
    fun _ => inferInstance
  exact Work.StemsB.SphRat.sigmaConstObjCompIso (MonoidalCategory.tensorRight M)
      (ModuleCat.of ℤ ℤ) ≪≫ Limits.sigmaConst.mapIso (λ_ M)

/-- **Explicit form of `Work.SSS.normalizedCoeffIso`.** -/
noncomputable def normalizedCoeffIsoIso (X : SSet) (M : ModuleCat ℤ) :
    X.normalizedChainComplex M ≅
      Work.SSS.expTens (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M :=
  normCoeff_coeffIso X M (sigmaConstTensorIsoIso M)

/-- **Explicit form of `Work.SSS.coprodComplex_iso`.** -/
noncomputable def coprodComplexIso {C : Type*} [Category C] [Preadditive C] {ι : Type}
    [HasColimitsOfShape (Discrete ι) C] (F : ι → ChainComplex C ℕ) :
    (∐ F) ≅ coprodComplex F :=
  (IsColimit.coconePointUniqueUpToIso (coprodComplex_isColimit F)
    (colimit.isColimit (Discrete.functor F))).symm

/-- **Explicit form of `Work.SSS.serreE1CoefIso`.** -/
noncomputable def serreE1CoefIsoIso (X : SSet.{0}) (M : ModuleCat ℤ) (d : ℕ) :
    (∐ (fun _ : Work.SSS.nIndex X d => M)) ≅
      (Work.SSS.tensorComplex (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).X d :=
  (coprodReindexIso X d M).symm ≪≫
    normalizedChainComplexCoprodIso X M d ≪≫
    asIso ((normalizedCoeffIsoIso X M).hom.f d) ≪≫
    (asIso ((tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ))
      M).hom.f d)).symm

end

end Work.SSS
