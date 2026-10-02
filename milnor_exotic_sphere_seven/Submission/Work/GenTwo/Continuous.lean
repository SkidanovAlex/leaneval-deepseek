import Mathlib
import Submission.Work.GenTwo.Bundles
import Submission.Work.GenTwo.BlockInverse
import Submission.Work.GenTwo.Model
import Submission.Work.Gen.gauge_continuous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Continuity of the Euler-sequence gauge of `ℂP²`

The `n = 2` instance of `Submission/Work/Gen/gauge_continuous.lean`: every map the gauge is built
from depends on `b` only through the chart coordinate `chartFun p b`, so continuity is continuity in
the chart variable together with the (by definition continuous) chart changes of `Tgt`.
-/

namespace Work.Gen.E2

open Work.Projective

noncomputable section

/-- `u ↦ blockFibre p u` is continuous. -/
lemma continuous_blockFibre (p : Fin 3) :
    Continuous (fun u : Fin 2 → ℂ => blockFibre p u) := by
  have hG : Continuous (fun u : Fin 2 → ℂ => GblockCLM p u) := Work.Gen.continuous_GblockCLM p
  have hH : Continuous (fun u : Fin 2 → ℂ => HblockCLM p u) := Work.Gen.continuous_HblockCLM p
  have hA : Continuous (fun u : Fin 2 → ℂ =>
      (wlpC 3).symm.toContinuousLinearMap.comp
        ((GblockCLM p u).comp
          (((holPart : EuclideanSpace ℂ (Fin (2 * 2)) →L[ℂ] (Fin 2 → ℂ)).comp
              (ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin (2 * 2))) (EuclideanSpace ℂ (Fin 2)))).prod
            (Work.Gen.c0CLM.comp
              (ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin (2 * 2))) (EuclideanSpace ℂ (Fin 2))))))) :=
    (hG.clm_comp_const _).const_clm_comp _
  have hB : Continuous (fun u : Fin 2 → ℂ =>
      (wlpC 3).symm.toContinuousLinearMap.comp
        ((HblockCLM p u).comp
          (((antiPart : EuclideanSpace ℂ (Fin (2 * 2)) →L[ℂ] (Fin 2 → ℂ)).comp
              (ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin (2 * 2))) (EuclideanSpace ℂ (Fin 2)))).prod
            (Work.Gen.c1CLM.comp
              (ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin (2 * 2))) (EuclideanSpace ℂ (Fin 2))))))) :=
    (hH.clm_comp_const _).const_clm_comp _
  rw [show (fun u : Fin 2 → ℂ => blockFibre p u) = fun u =>
      ((wlpC 3).symm.toContinuousLinearMap.comp
        ((GblockCLM p u).comp
          (((holPart : EuclideanSpace ℂ (Fin (2 * 2)) →L[ℂ] (Fin 2 → ℂ)).comp
              (ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin (2 * 2))) (EuclideanSpace ℂ (Fin 2)))).prod
            (Work.Gen.c0CLM.comp
              (ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin (2 * 2))) (EuclideanSpace ℂ (Fin 2))))))).prod
      ((wlpC 3).symm.toContinuousLinearMap.comp
        ((HblockCLM p u).comp
          (((antiPart : EuclideanSpace ℂ (Fin (2 * 2)) →L[ℂ] (Fin 2 → ℂ)).comp
              (ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin (2 * 2))) (EuclideanSpace ℂ (Fin 2)))).prod
            (Work.Gen.c1CLM.comp
              (ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin (2 * 2))) (EuclideanSpace ℂ (Fin 2))))))) from by
        funext u; rw [blockFibre]]
  exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp (hA.prodMk hB)

/-- `u ↦ blockInv p u` is continuous. -/
lemma continuous_blockInv (p : Fin 3) :
    Continuous (fun u : Fin 2 → ℂ => blockInv p u) := by
  have hGi : Continuous (fun u : Fin 2 → ℂ => GblockInv p u) := Work.Gen.continuous_GblockInv p
  have hHi : Continuous (fun u : Fin 2 → ℂ => HblockInv p u) := Work.Gen.continuous_HblockInv p
  have hA : Continuous (fun u : Fin 2 → ℂ => blkA p u) :=
    (hGi.clm_comp_const _).const_clm_comp _
  have hB : Continuous (fun u : Fin 2 → ℂ => blkB p u) :=
    (hHi.clm_comp_const _).const_clm_comp _
  have hC : Continuous (fun u : Fin 2 → ℂ => blkC p u) :=
    (hGi.clm_comp_const _).const_clm_comp _
  have hD : Continuous (fun u : Fin 2 → ℂ => blkD p u) :=
    (hHi.clm_comp_const _).const_clm_comp _
  have hAB : Continuous (fun u : Fin 2 → ℂ => (blkA p u).prod (blkB p u)) :=
    (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp (hA.prodMk hB)
  have h1 : Continuous (fun u : Fin 2 → ℂ =>
      XiEquiv.toContinuousLinearMap.comp ((blkA p u).prod (blkB p u))) :=
    hAB.const_clm_comp _
  have hCD : Continuous (fun u : Fin 2 → ℂ => (blkC p u).prod (blkD p u)) :=
    (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp (hC.prodMk hD)
  have h2 : Continuous (fun u : Fin 2 → ℂ =>
      Work.Gen.pair2CLM.comp ((blkC p u).prod (blkD p u))) :=
    hCD.const_clm_comp _
  rw [show (fun u : Fin 2 → ℂ => blockInv p u) = fun u =>
      (XiEquiv.toContinuousLinearMap.comp ((blkA p u).prod (blkB p u))).prod
        (Work.Gen.pair2CLM.comp ((blkC p u).prod (blkD p u))) from by
        funext u; rw [blockInv]]
  exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp (h1.prodMk h2)

/-- `b ↦ MCLM p b` is continuous on the chart `p`. -/
lemma continuousOn_MCLM (p : Fin 3) :
    ContinuousOn (fun b : CP 2 => MCLM p b) (chartSet p) := by
  have hbf : Continuous (fun u : Fin 2 → ℂ => blockFibre p u) := continuous_blockFibre p
  have h1 : Continuous (fun u : Fin 2 → ℂ =>
      (blockFibre p u).comp (Work.Whitney.sumFibreC (2 * 2) 2).symm.toContinuousLinearMap) :=
    hbf.clm_comp_const _
  have h2 : Continuous (fun u : Fin 2 → ℂ => CbigCLM.comp
      ((blockFibre p u).comp (Work.Whitney.sumFibreC (2 * 2) 2).symm.toContinuousLinearMap)) :=
    h1.const_clm_comp CbigCLM
  refine (h2.comp_continuousOn (continuousOn_chartFun p)).congr (fun b _ => ?_)
  show MCLM p b = CbigCLM.comp ((blockFibre p (chartFun p b)).comp
    (Work.Whitney.sumFibreC (2 * 2) 2).symm.toContinuousLinearMap)
  rw [MCLM]

/-- `b ↦ MInvCLM p b` is continuous on the chart `p`. -/
lemma continuousOn_MInvCLM (p : Fin 3) :
    ContinuousOn (fun b : CP 2 => MInvCLM p b) (chartSet p) := by
  have hbi : Continuous (fun u : Fin 2 → ℂ => blockInv p u) := continuous_blockInv p
  have h1 : Continuous (fun u : Fin 2 → ℂ => (blockInv p u).comp CbigInv) :=
    hbi.clm_comp_const _
  have h2 : Continuous (fun u : Fin 2 → ℂ =>
      (Work.Whitney.sumFibreC (2 * 2) 2).toContinuousLinearMap.comp
        ((blockInv p u).comp CbigInv)) :=
    h1.const_clm_comp _
  refine (h2.comp_continuousOn (continuousOn_chartFun p)).congr (fun b _ => ?_)
  show MInvCLM p b = (Work.Whitney.sumFibreC (2 * 2) 2).toContinuousLinearMap.comp
    ((blockInv p (chartFun p b)).comp CbigInv)
  rw [MInvCLM]

/-- `b ↦ gaugeCLM p t b` is continuous on `Src.baseSet (p,β) ∩ Tgt.baseSet t`. -/
lemma continuousOn_gaugeCLM (p : Fin 3) (β : Fin 1) (t : TgtIdx) :
    ContinuousOn (fun b : CP 2 => gaugeCLM p t b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) := by
  have hsub1 : Src.baseSet (p, β) ∩ Tgt.baseSet t ⊆ chartSet p := by
    intro b hb
    rw [Src_baseSet] at hb
    exact hb.1
  have hsub2 : Src.baseSet (p, β) ∩ Tgt.baseSet t ⊆ Tgt.baseSet (diagIdx p) ∩ Tgt.baseSet t := by
    intro b hb
    rw [Tgt_baseSet_diagIdx]
    exact ⟨hsub1 hb, hb.2⟩
  have hA : ContinuousOn (fun b : CP 2 => Tgt.coordChange (diagIdx p) t b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) :=
    (Tgt.continuousOn_coordChange (diagIdx p) t).mono hsub2
  have hB : ContinuousOn (fun b : CP 2 => MCLM p b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) :=
    (continuousOn_MCLM p).mono hsub1
  refine (hA.clm_comp hB).congr (fun b _ => ?_)
  rw [gaugeCLM]

/-- `b ↦ gaugeInvCLM p t b` is continuous on `Src.baseSet (p,β) ∩ Tgt.baseSet t`. -/
lemma continuousOn_gaugeInvCLM (p : Fin 3) (β : Fin 1) (t : TgtIdx) :
    ContinuousOn (fun b : CP 2 => gaugeInvCLM p t b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) := by
  have hsub1 : Src.baseSet (p, β) ∩ Tgt.baseSet t ⊆ chartSet p := by
    intro b hb
    rw [Src_baseSet] at hb
    exact hb.1
  have hsub2 : Src.baseSet (p, β) ∩ Tgt.baseSet t ⊆ Tgt.baseSet t ∩ Tgt.baseSet (diagIdx p) := by
    intro b hb
    rw [Tgt_baseSet_diagIdx]
    exact ⟨hb.2, hsub1 hb⟩
  have hA : ContinuousOn (fun b : CP 2 => Tgt.coordChange t (diagIdx p) b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) :=
    (Tgt.continuousOn_coordChange t (diagIdx p)).mono hsub2
  have hB : ContinuousOn (fun b : CP 2 => MInvCLM p b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) :=
    (continuousOn_MInvCLM p).mono hsub1
  refine (hB.clm_comp hA).congr (fun b _ => ?_)
  rw [gaugeInvCLM]

/-- **Continuity of the gauge of the complexified Euler sequence of `ℂP²`.** -/
theorem gauge_continuous :
    (∀ (p : Fin 3), ContinuousOn (fun b : Work.Projective.CP 2 => Work.Gen.E2.MCLM p b)
      (Work.Projective.chartSet p)) ∧
    (∀ (p : Fin 3), ContinuousOn (fun b : Work.Projective.CP 2 => Work.Gen.E2.MInvCLM p b)
      (Work.Projective.chartSet p)) ∧
    (∀ (p : Fin 3) (β : Fin 1) (t : Work.Gen.E2.TgtIdx),
      ContinuousOn (fun b : Work.Projective.CP 2 => Work.Gen.E2.gaugeCLM p t b)
        (Work.Gen.E2.Src.baseSet (p, β) ∩ Work.Gen.E2.Tgt.baseSet t)) ∧
    (∀ (p : Fin 3) (β : Fin 1) (t : Work.Gen.E2.TgtIdx),
      ContinuousOn (fun b : Work.Projective.CP 2 => Work.Gen.E2.gaugeInvCLM p t b)
        (Work.Gen.E2.Src.baseSet (p, β) ∩ Work.Gen.E2.Tgt.baseSet t)) :=
  ⟨continuousOn_MCLM, continuousOn_MInvCLM, continuousOn_gaugeCLM, continuousOn_gaugeInvCLM⟩

end

end Work.Gen.E2
