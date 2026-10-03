import Mathlib
import Submission.Work.OROneRel.mmVertexDataDefs
import Submission.Work.OROneRel.mmStepData_of_expsum_zero

namespace Work.OROneRel

theorem mmStepData_vertexData_expZero {α : Type*} (r : FreeGroup α) (t : α)
    (hF : ∀ {γ : Type*} (s : FreeGroup γ), Work.OROneRel.FreiheitssatzAt s)
    (hr : Work.OROneRel.IsCyclicallyReducedRelator r) (h1 : r ≠ 1)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (h : Work.OROneRel.eps t r = 0) :
    Work.OROneRel.HasMMVertexData r (Work.OROneRel.mmBeta t r) (Work.OROneRel.mmW t r) := by
  classical
  have hFw : FreiheitssatzAt (mmW t r) := freiheitssatzAt_of_forall (mmW t r) hF
  have hred : FreeGroup.IsReduced (mmWL t r) := mmWL_isReduced t r hr h
  have hc : IsCyclicallyReducedRelator (mmW t r) := mmW_isCyclicallyReduced hr h
  have hA : (mmW t r) ∉ Subgroup.closure (FreeGroup.of '' mmTA t r) :=
    mmW_notMem_closure_TA h1 ht h hred
  have hB : (mmW t r) ∉ Subgroup.closure (FreeGroup.of '' mmTB t r) :=
    mmW_notMem_closure_TB h1 ht h hred
  have hrel : FreeGroup.lift (mmThetaFun hFw hc hA hB) r = 1 :=
    mmThetaFun_relator h hFw hc hA hB
  have hC2 : (mmPsi h hFw hc hA hB).comp (mmTheta hFw hc hA hB hrel) = MonoidHom.id (mmG r) :=
    mmPsi_comp_mmTheta h hFw hc hA hB hrel
  have hC3 : (mmTheta hFw hc hA hB hrel).comp (mmPsi h hFw hc hA hB) =
      MonoidHom.id (mmK t r hFw hc hA hB) :=
    mmTheta_comp_mmPsi h hFw hc hA hB hrel
  refine ⟨Or.inr ⟨hc, mmW_ne_one hred (mmWL_ne_nil h1 ht h)⟩,
    mmA t r, mmB t r, ⟨mmTA t r, hA, rfl⟩, ⟨mmTB t r, hB, rfl⟩, mmPhi hFw hc hA hB, ?_⟩
  exact ⟨(MonoidHom.toMulEquiv (mmPsi h hFw hc hA hB) (mmTheta hFw hc hA hB hrel)
    hC3 hC2).symm⟩

end Work.OROneRel
