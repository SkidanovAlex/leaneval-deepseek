import Mathlib
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The constant-gauge bundle isomorphism, with a plain map of covers

`Work.Whitney.nonempty_bundleIso_of_gauge_fibre` produces a `Work.Thom.BundleIso` from a constant
gauge `e : F ≃L[𝕜] F'` of the model fibres and a compatibility of the two covers.  It asks for an
*equivalence* `σ : ι ≃ ι'` of the covers, but its proof only ever applies `σ` to an index -- the
inverse is never used, and neither is injectivity nor surjectivity.

This module records the corresponding lemma for a plain function `σ : ι → ι'`, which is what the
distributivity `L ⊗ (E ⊕ F) ≅ (L ⊗ E) ⊕ (L ⊗ F)` needs: there the natural index map
`(l, (e, f)) ↦ ((l, e), (l, f))` embeds `ιL × (ιE × ιF)` into `(ιL × ιE) × (ιL × ιF)` but is far
from surjective, since the two `ιL`-coordinates of a pair in the target need not agree.
-/

namespace Work.LerayHirsch

open Work.TangentClasses

noncomputable section

theorem nonempty_bundleIso_of_gauge_fibre_map {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B] {F F' : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {ι ι' : Type*} (X : VectorBundleCore 𝕜 B F ι) (Y : VectorBundleCore 𝕜 B F' ι')
    (e : F ≃L[𝕜] F') (σ : ι → ι')
    (hbase : ∀ i : ι, Y.baseSet (σ i) = X.baseSet i)
    (hindex : ∀ b : B, Y.indexAt b = σ (X.indexAt b))
    (hconj : ∀ (i : ι) (b : B),
      (Y.coordChange (Y.indexAt b) (σ i) b).comp ((e : F →L[𝕜] F'))
        = ((e : F →L[𝕜] F')).comp (X.coordChange (X.indexAt b) i b)) :
    Nonempty (Work.Thom.BundleIso X Y) := by
  -- `hindex` lets one read the transition functions of `Y` in the chart of `X`.
  have hconj' : ∀ (i : ι) (b : B),
      (Y.coordChange (σ (X.indexAt b)) (σ i) b).comp ((e : F →L[𝕜] F'))
        = ((e : F →L[𝕜] F')).comp (X.coordChange (X.indexAt b) i b) := by
    intro i b
    rw [← hindex b]
    exact hconj i b
  -- Continuity of the total-space map `X → Y`, chart by chart: on `X.baseSet i₁ ∩ Y.baseSet i₂`
  -- the conjugate of the gauge is, by `hconj` and `coordChange_comp`, `Y.coordChange (σ i₁) i₂ ∘ e`.
  have hT : ∀ (i₁ : ι) (i₂ : ι'), ContinuousOn (fun b : B =>
      (Y.coordChange (Y.indexAt b) i₂ b).comp (((e : F →L[𝕜] F').comp
        (X.coordChange i₁ (X.indexAt b) b)))) (X.baseSet i₁ ∩ Y.baseSet i₂) := by
    intro i₁ i₂
    refine ContinuousOn.congr (f := fun b : B =>
      (Y.coordChange (σ i₁) i₂ b).comp (e : F →L[𝕜] F')) ?_ ?_
    · refine ContinuousOn.clm_comp ?_ continuousOn_const
      exact (Y.continuousOn_coordChange (σ i₁) i₂).mono
        (fun b hb => ⟨by rw [hbase i₁]; exact hb.1, hb.2⟩)
    · intro b hb
      have hbX : b ∈ X.baseSet i₁ := hb.1
      have hbY2 : b ∈ Y.baseSet i₂ := hb.2
      have hbY1 : b ∈ Y.baseSet (σ i₁) := by rw [hbase i₁]; exact hbX
      have hcomp : (Y.coordChange (Y.indexAt b) i₂ b)
          = (Y.coordChange (σ i₁) i₂ b).comp (Y.coordChange (Y.indexAt b) (σ i₁) b) :=
        (Y.coordChange_linear_comp (Y.indexAt b) (σ i₁) i₂ b
          ⟨⟨Y.mem_baseSet_at b, hbY1⟩, hbY2⟩).symm
      have hXc : (X.coordChange (X.indexAt b) i₁ b).comp
          (X.coordChange i₁ (X.indexAt b) b) = ContinuousLinearMap.id 𝕜 F := by
        rw [X.coordChange_linear_comp i₁ (X.indexAt b) i₁ b
          ⟨⟨hbX, X.mem_baseSet_at b⟩, hbX⟩]
        ext v
        exact X.coordChange_self i₁ b hbX v
      calc (Y.coordChange (Y.indexAt b) i₂ b).comp ((e : F →L[𝕜] F').comp
              (X.coordChange i₁ (X.indexAt b) b))
          = ((Y.coordChange (σ i₁) i₂ b).comp (Y.coordChange (Y.indexAt b) (σ i₁) b)).comp
              ((e : F →L[𝕜] F').comp (X.coordChange i₁ (X.indexAt b) b)) := by rw [hcomp]
        _ = (Y.coordChange (σ i₁) i₂ b).comp ((Y.coordChange (Y.indexAt b) (σ i₁) b).comp
              ((e : F →L[𝕜] F').comp (X.coordChange i₁ (X.indexAt b) b))) := by
              rw [ContinuousLinearMap.comp_assoc]
        _ = (Y.coordChange (σ i₁) i₂ b).comp (((Y.coordChange (Y.indexAt b) (σ i₁) b).comp
              (e : F →L[𝕜] F')).comp (X.coordChange i₁ (X.indexAt b) b)) := by
              rw [ContinuousLinearMap.comp_assoc]
        _ = (Y.coordChange (σ i₁) i₂ b).comp (((e : F →L[𝕜] F').comp
              (X.coordChange (X.indexAt b) i₁ b)).comp
              (X.coordChange i₁ (X.indexAt b) b)) := by rw [hindex b, hconj' i₁ b]
        _ = (Y.coordChange (σ i₁) i₂ b).comp ((e : F →L[𝕜] F').comp
              ((X.coordChange (X.indexAt b) i₁ b).comp (X.coordChange i₁ (X.indexAt b) b))) := by
              rw [ContinuousLinearMap.comp_assoc]
        _ = (Y.coordChange (σ i₁) i₂ b).comp ((e : F →L[𝕜] F').comp
              (ContinuousLinearMap.id 𝕜 F)) := by rw [hXc]
        _ = (Y.coordChange (σ i₁) i₂ b).comp (e : F →L[𝕜] F') := by
              rw [ContinuousLinearMap.comp_id]
  -- The same for `Y → X` with the inverse gauge; the conjugation identity for `e.symm` is
  -- obtained from `hconj` by composing with `e.symm` on both sides.
  have hTi : ∀ (i₂ : ι') (i₁ : ι), ContinuousOn (fun b : B =>
      (X.coordChange (X.indexAt b) i₁ b).comp (((e.symm : F' →L[𝕜] F).comp
        (Y.coordChange i₂ (Y.indexAt b) b)))) (Y.baseSet i₂ ∩ X.baseSet i₁) := by
    intro i₂ i₁
    refine ContinuousOn.congr (f := fun b : B =>
      ((e.symm : F' →L[𝕜] F)).comp (Y.coordChange i₂ (σ i₁) b)) ?_ ?_
    · refine ContinuousOn.clm_comp continuousOn_const ?_
      exact (Y.continuousOn_coordChange i₂ (σ i₁)).mono
        (fun b hb => ⟨hb.1, by rw [hbase i₁]; exact hb.2⟩)
    · intro b hb
      have hbY2 : b ∈ Y.baseSet i₂ := hb.1
      have hbX1 : b ∈ X.baseSet i₁ := hb.2
      have hbY1 : b ∈ Y.baseSet (σ i₁) := by rw [hbase i₁]; exact hbX1
      have hrev : (X.coordChange (X.indexAt b) i₁ b).comp ((e.symm : F' →L[𝕜] F))
          = ((e.symm : F' →L[𝕜] F)).comp (Y.coordChange (Y.indexAt b) (σ i₁) b) := by
        apply ContinuousLinearMap.ext
        intro w
        simp only [ContinuousLinearMap.comp_apply]
        have h2 : (Y.coordChange (Y.indexAt b) (σ i₁) b)
              ((e : F →L[𝕜] F') ((e.symm : F' →L[𝕜] F) w))
            = (e : F →L[𝕜] F')
              ((X.coordChange (X.indexAt b) i₁ b) ((e.symm : F' →L[𝕜] F) w)) := by
          have h3 := congrArg (fun (L : F →L[𝕜] F') => L ((e.symm : F' →L[𝕜] F) w))
            (hconj i₁ b)
          simpa only [ContinuousLinearMap.comp_apply] using h3
        calc (X.coordChange (X.indexAt b) i₁ b) ((e.symm : F' →L[𝕜] F) w)
            = (e.symm : F' →L[𝕜] F)
                ((e : F →L[𝕜] F')
                  ((X.coordChange (X.indexAt b) i₁ b) ((e.symm : F' →L[𝕜] F) w))) := by
                simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
          _ = (e.symm : F' →L[𝕜] F)
                ((Y.coordChange (Y.indexAt b) (σ i₁) b)
                  ((e : F →L[𝕜] F') ((e.symm : F' →L[𝕜] F) w))) := by rw [h2]
          _ = (e.symm : F' →L[𝕜] F) ((Y.coordChange (Y.indexAt b) (σ i₁) b) w) := by
                simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
      have hcomp2 : (Y.coordChange (Y.indexAt b) (σ i₁) b).comp
            (Y.coordChange i₂ (Y.indexAt b) b) = Y.coordChange i₂ (σ i₁) b :=
        Y.coordChange_linear_comp i₂ (Y.indexAt b) (σ i₁) b
          ⟨⟨hbY2, Y.mem_baseSet_at b⟩, hbY1⟩
      calc (X.coordChange (X.indexAt b) i₁ b).comp (((e.symm : F' →L[𝕜] F)).comp
              (Y.coordChange i₂ (Y.indexAt b) b))
          = (((X.coordChange (X.indexAt b) i₁ b).comp (e.symm : F' →L[𝕜] F)).comp
              (Y.coordChange i₂ (Y.indexAt b) b)) := by
              rw [← ContinuousLinearMap.comp_assoc]
        _ = (((e.symm : F' →L[𝕜] F)).comp (Y.coordChange (Y.indexAt b) (σ i₁) b)).comp
              (Y.coordChange i₂ (Y.indexAt b) b) := by rw [hrev]
        _ = ((e.symm : F' →L[𝕜] F)).comp ((Y.coordChange (Y.indexAt b) (σ i₁) b).comp
              (Y.coordChange i₂ (Y.indexAt b) b)) := by
              rw [ContinuousLinearMap.comp_assoc]
        _ = ((e.symm : F' →L[𝕜] F)).comp (Y.coordChange i₂ (σ i₁) b) := by rw [hcomp2]
  refine ⟨{ hom := fun _ => (e : F →L[𝕜] F').toLinearMap
            inv := fun _ => (e.symm : F' →L[𝕜] F).toLinearMap
            left_inv := fun b x => ?_
            right_inv := fun b y => ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · exact e.symm_apply_apply x
  · exact e.apply_symm_apply y
  · have hc : Continuous (fun p : X.TotalSpace =>
        (⟨p.1, (e : F →L[𝕜] F') p.2⟩ : Y.TotalSpace)) := by
      have hc0 := Work.Thom.continuous_totalSpaceMap_clm_gen X Y (ContinuousMap.id B)
        (fun _ => (e : F →L[𝕜] F')) (by
          intro i₁ i₂
          simpa only [ContinuousMap.coe_id, Set.preimage_id, ContinuousMap.id_apply] using hT i₁ i₂)
      simpa only [ContinuousMap.id_apply] using hc0
    refine Continuous.congr hc (fun p => ?_)
    exact congrArg (fun w : F' => (⟨p.1, w⟩ : Y.TotalSpace))
      (congrFun (ContinuousLinearMap.coe_coe (e : F →L[𝕜] F')).symm p.2)
  · have hc : Continuous (fun p : Y.TotalSpace =>
        (⟨p.1, (e.symm : F' →L[𝕜] F) p.2⟩ : X.TotalSpace)) := by
      have hc0 := Work.Thom.continuous_totalSpaceMap_clm_gen Y X (ContinuousMap.id B)
        (fun _ => (e.symm : F' →L[𝕜] F)) (by
          intro i₂ i₁
          simpa only [ContinuousMap.coe_id, Set.preimage_id, ContinuousMap.id_apply] using hTi i₂ i₁)
      simpa only [ContinuousMap.id_apply] using hc0
    refine Continuous.congr hc (fun p => ?_)
    exact congrArg (fun w : F => (⟨p.1, w⟩ : X.TotalSpace))
      (congrFun (ContinuousLinearMap.coe_coe (e.symm : F' →L[𝕜] F)).symm p.2)

end

end Work.LerayHirsch
