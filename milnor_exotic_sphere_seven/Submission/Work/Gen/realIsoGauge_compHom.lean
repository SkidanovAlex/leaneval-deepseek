import Mathlib
import Submission.Work.Gen.RealIsoGaugeDefs
import Submission.Work.Thom.isoGauge_data

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.Gen

open Work.Thom Work.TangentClasses

noncomputable section

/-- The chart homeomorphism of `realification Z'`, precomposed with the piece map of a real
isomorphism `e` of the realifications, is the gauge endomorphism of `realIsoGauge`, postcomposed
with the chart homeomorphism of `realification Z`. -/
theorem realIsoGauge_compHom {m : ℕ} {B : Type} [TopologicalSpace B] {ι ι' : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : Work.Thom.BundleIso (Work.Thom.realification Z) (Work.Thom.realification Z'))
    (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ (Work.Thom.realification Z).baseSet i)
    (hWi' : W ⊆ (Work.Thom.realification Z').baseSet i')
    (hc : Continuous (Work.Gen.realIsoGauge Z Z' e i i' hWi hWi')) :
    (Work.Thom.chartHomeo (Work.Thom.realification Z') (2 * m) Work.Thom.covE i' W hWi' :
        C(↥((Work.Thom.realification Z').proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m)))).comp
        (Work.Gen.realPieceMap (Work.Thom.realification Z) (Work.Thom.realification Z') e W)
      = (Work.Thom.gaugeEnd (Work.Gen.realIsoGauge Z Z' e i i' hWi hWi') hc :
            C(↥W × EuclideanSpace ℝ (Fin (2 * m)), ↥W × EuclideanSpace ℝ (Fin (2 * m)))).comp
          (Work.Thom.chartHomeo (Work.Thom.realification Z) (2 * m) Work.Thom.covE i W hWi :
            C(↥((Work.Thom.realification Z).proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m)))) := by
  apply ContinuousMap.ext
  intro p
  change (chartHomeo (realification Z') (2 * m) covE i' W hWi')
        (realPieceMap (realification Z) (realification Z') e W p)
      = gaugeEnd (realIsoGauge Z Z' e i i' hWi hWi') hc
          (chartHomeo (realification Z) (2 * m) covE i W hWi p)
  have hq : realPieceMap (realification Z) (realification Z') e W p =
      (⟨⟨(realification Z).proj p.1, e.hom ((realification Z).proj p.1) p.1.2⟩, p.2⟩ :
        ↥((realification Z').proj ⁻¹' W)) := by
    apply Subtype.ext
    rw [realPieceMap_apply, BundleIso.toTotalSpace_apply]
  rw [hq, chartHomeo_apply]
  rw [gaugeEnd_apply, chartHomeo_apply]
  rw [realIsoGauge_apply]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  have hcoc : ((realification Z).coordChange i
        ((realification Z).indexAt ((realification Z).proj p.1)) ((realification Z).proj p.1))
        (((realification Z).coordChange ((realification Z).indexAt ((realification Z).proj p.1)) i
          ((realification Z).proj p.1)) p.1.2)
      = p.1.2 := by
    have hmem' : (realification Z).proj p.1 ∈
        (realification Z).baseSet ((realification Z).indexAt ((realification Z).proj p.1))
          ∩ (realification Z).baseSet i
          ∩ (realification Z).baseSet ((realification Z).indexAt ((realification Z).proj p.1)) :=
      ⟨⟨(realification Z).mem_baseSet_at _, hWi p.2⟩, (realification Z).mem_baseSet_at _⟩
    have h1 := VectorBundleCore.coordChange_comp (realification Z)
      ((realification Z).indexAt ((realification Z).proj p.1)) i
      ((realification Z).indexAt ((realification Z).proj p.1)) ((realification Z).proj p.1) hmem'
      p.1.2
    have h2 := VectorBundleCore.coordChange_self (realification Z)
      ((realification Z).indexAt ((realification Z).proj p.1)) ((realification Z).proj p.1)
      ((realification Z).mem_baseSet_at _) p.1.2
    exact h1.trans h2
  rw [hcoc]
  refine Prod.ext ?_ ?_
  · apply Subtype.ext; rfl
  · rfl

end

end Work.Gen
