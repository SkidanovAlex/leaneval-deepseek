import Mathlib
import Submission.Work.Gen.EulerBlockGauge
import Submission.Work.Gen.EulerBlockInverse
import Submission.Work.Gen.cbigDiagCLM

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# The gauge identity of the Euler sequence

`Work.Gen.gaugeCore`: on the overlap of two charts, the block gauge `MCLM` commutes with the
transition functions of the source and the target bundle of the Euler sequence,
`MCLM q ∘ Src.coordChange (p → q) = Tgt.coordChange (diag p → diag q) ∘ MCLM p`.
-/

namespace Work.Gen

open Work.Projective

noncomputable section

theorem Src_coordChange (p q : Fin 5) (β β' : Fin 1) (b : CP 4) :
    Src.coordChange (p, β) (q, β') b
      = (Work.Whitney.sumFibreC 8 2 : (EuclideanSpace ℂ (Fin 8) × EuclideanSpace ℂ (Fin 2)) →L[ℂ]
          EuclideanSpace ℂ (Fin (8 + 2))).comp
        (((Work.Thom.cxTrans (stdTangentReal.coordChange p q b)).prodMap
            (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)))).comp
          ((Work.Whitney.sumFibreC 8 2).symm : EuclideanSpace ℂ (Fin (8 + 2)) →L[ℂ]
            (EuclideanSpace ℂ (Fin 8) × EuclideanSpace ℂ (Fin 2)))) := by
  have h1 : (stdTangentC 4).coordChange p q b
      = Work.Thom.cxTrans (stdTangentReal.coordChange p q b) := by
    rw [stdTangentC_eq]; rfl
  have h2 : (trivialVectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 2)) (Fin 1)).coordChange
      β β' b = 1 := rfl
  rw [Src, Work.Whitney.whitneySum_coordChange, h1, h2]
  rfl

theorem T4_fderiv_eq (p q : Fin 5) {b : CP 4} (hb : b ∈ chartSet p ∩ chartSet q) :
    T4 (fderiv ℂ (Phi p q) (chartFun p b)) = stdTangentReal.coordChange p q b := by
  rw [tangentCoordChange_stdChart p q b hb]
  rfl

/-- **The gauge identity of the block gauge**, in the form of an identity of continuous linear
maps. -/
theorem blockGaugeCLM (p q : Fin 5) {b : CP 4} (hb : b ∈ chartSet p ∩ chartSet q) :
    (blockFibre q (chartFun q b)).comp
        ((Work.Thom.cxTrans (T4 (fderiv ℂ (Phi p q) (chartFun p b)))).prodMap
          (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2))))
      = (((homCoord 4 q p b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 5))).prodMap
          ((homCoord 4 p q b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 5)))).comp
        (blockFibre p (chartFun p b)) := by
  apply ContinuousLinearMap.ext
  rintro ⟨ξ, c⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  show blockFibre q (chartFun q b)
      ((Work.Thom.cxTrans (T4 (fderiv ℂ (Phi p q) (chartFun p b))) ξ, c))
    = ((homCoord 4 q p b) • (blockFibre p (chartFun p b) (ξ, c)).1,
       (homCoord 4 p q b) • (blockFibre p (chartFun p b) (ξ, c)).2)
  exact blockGauge p q hb ξ c

/-- **The gauge identity of the Euler sequence.** -/
theorem gaugeCore (p q : Fin 5) {b : CP 4} (hb : b ∈ chartSet p ∩ chartSet q) :
    (MCLM q b).comp (Src.coordChange (p, 0) (q, 0) b)
      = (Tgt.coordChange (diagIdx p) (diagIdx q) b).comp (MCLM p b) := by
  rw [Src_coordChange, MCLM, MCLM, cbigDiagCLM p q b hb, ← T4_fderiv_eq p q hb]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  set e := Work.Whitney.sumFibreC 8 2 with he
  set L := T4 (fderiv ℂ (Phi p q) (chartFun p b)) with hL
  set w : EuclideanSpace ℂ (Fin 8) × EuclideanSpace ℂ (Fin 2) :=
    (e.symm.toContinuousLinearMap x) with hw
  have hcancel : ∀ z : EuclideanSpace ℂ (Fin 8) × EuclideanSpace ℂ (Fin 2),
      e.symm.toContinuousLinearMap (e.toContinuousLinearMap z) = z :=
    fun z => ContinuousLinearEquiv.symm_apply_apply e z
  have hpair : ∀ z : EuclideanSpace ℂ (Fin 8) × EuclideanSpace ℂ (Fin 2),
      ((Work.Thom.cxTrans L).prodMap (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)))) z
        = ((Work.Thom.cxTrans L) z.1, z.2) :=
    fun z => rfl
  rw [hpair, hcancel]
  rw [blockGauge p q hb _ _]
  rw [CbigInv_CbigCLM, Prod.mk.eta]
  rfl

end

end Work.Gen
