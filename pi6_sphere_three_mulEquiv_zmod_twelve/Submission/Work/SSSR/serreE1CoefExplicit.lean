import Mathlib
import Submission.Work.SSSR.serreE1CoefIso
import Submission.Work.SSSR.tensorComplexIsoExpTens
import Submission.Work.SSSR.normalizedCoeffIso
import Submission.Work.SSSR.HomologySigmaAux
import Submission.Work.SSSR.coprodComplex_iso
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped MonoidalCategory
noncomputable section

/-- **Explicit form of `Work.SSSR.tensorComplexIsoExpTens`.**  The tensor complex `K ⊗ M` is the
naive coefficient extension `expTens K M`, via the inverse of the explicit chain isomorphism
`split K M` (whose inverse is supplied degreewise by `collapseX`). -/
noncomputable def tensorComplexIsoExpTensIso (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) :
    Work.SSSR.tensorComplex R K M ≅ Work.SSSR.expTens K M := by
  haveI : ∀ n, IsIso ((split K M).f n) := fun n =>
    ⟨collapseX K M n, splitX_collapseX K M n, collapseX_splitX K M n⟩
  haveI : IsIso (split K M) := HomologicalComplex.Hom.isIso_of_components _
  exact (asIso (split K M)).symm

/-- **Explicit form of `Work.SSSR.sigmaConstTensorIso`.** -/
noncomputable def sigmaConstTensorIsoIso (M : ModuleCat R) :
    (Limits.sigmaConst.obj (ModuleCat.of R R) ⋙ MonoidalCategory.tensorRight M :
        Type ⥤ ModuleCat R) ≅
      (Limits.sigmaConst.obj M : Type ⥤ ModuleCat R) := by
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S) (MonoidalCategory.tensorRight M) :=
    fun _ => inferInstance
  exact Work.SSSR.StemsB.SphRat.sigmaConstObjCompIso (MonoidalCategory.tensorRight M)
      (ModuleCat.of R R) ≪≫ Limits.sigmaConst.mapIso (λ_ M)

/-- **Explicit form of `Work.SSSR.normalizedCoeffIso`.** -/
noncomputable def normalizedCoeffIsoIso (X : SSet) (M : ModuleCat R) :
    X.normalizedChainComplex M ≅
      Work.SSSR.expTens (X.normalizedChainComplex (ModuleCat.of R R)) M :=
  normCoeff_coeffIso X M (sigmaConstTensorIsoIso M)

/-- **Explicit form of `Work.SSSR.coprodComplex_iso`.** -/
noncomputable def coprodComplexIso {C : Type*} [Category C] [Preadditive C] {ι : Type}
    [HasColimitsOfShape (Discrete ι) C] (F : ι → ChainComplex C ℕ) :
    (∐ F) ≅ coprodComplex F :=
  (IsColimit.coconePointUniqueUpToIso (coprodComplex_isColimit F)
    (colimit.isColimit (Discrete.functor F))).symm

/-- **Explicit form of `Work.SSSR.serreE1CoefIso`.** -/
noncomputable def serreE1CoefIsoIso (X : SSet.{0}) (M : ModuleCat R) (d : ℕ) :
    (∐ (fun _ : Work.SSSR.nIndex X d => M)) ≅
      (Work.SSSR.tensorComplex R (X.normalizedChainComplex (ModuleCat.of R R)) M).X d :=
  (coprodReindexIso X d M).symm ≪≫
    normalizedChainComplexCoprodIso X M d ≪≫
    asIso ((normalizedCoeffIsoIso X M).hom.f d) ≪≫
    (asIso ((tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of R R))
      M).hom.f d)).symm

end

end Work.SSSR
