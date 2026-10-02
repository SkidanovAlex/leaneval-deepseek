import Mathlib
import Submission.Work.Thom.Iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Continuity of the total-space map of a field-general bundle morphism
-/

namespace Work.Thom

open Bundle

noncomputable section

/-- **Continuity of the total-space map of a bundle morphism over `f`, with a varying fibre map.**
If `T : B' → (F →L[𝕜] F')` is such that, in every pair of charts `(i₁, i₂)`, the trivialised matrix
`b ↦ Z₂.coordChange (Z₂.indexAt (f b)) i₂ (f b) ∘ T b ∘ Z₁.coordChange i₁ (Z₁.indexAt b) b` is
continuous on the overlap, then `⟨x, v⟩ ↦ ⟨f x, T x v⟩` is a continuous map of total spaces. -/
theorem continuous_totalSpaceMap_clm {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {ι ι' : Type} (Z₁ : VectorBundleCore 𝕜 B' F ι) (Z₂ : VectorBundleCore 𝕜 B F' ι')
    (f : C(B', B)) (T : B' → F →L[𝕜] F')
    (hT : ∀ (i₁ : ι) (i₂ : ι'), ContinuousOn (fun b : B' =>
        (Z₂.coordChange (Z₂.indexAt (f b)) i₂ (f b)).comp
          ((T b).comp (Z₁.coordChange i₁ (Z₁.indexAt b) b)))
        (Z₁.baseSet i₁ ∩ f ⁻¹' Z₂.baseSet i₂)) :
    Continuous (fun p : Z₁.TotalSpace => (⟨f p.1, T p.1 p.2⟩ : Z₂.TotalSpace)) := by
  have hgOn : ∀ (i₁ : ι) (i₂ : ι'),
      ContinuousOn (fun p : Z₁.TotalSpace => (⟨f p.1, T p.1 p.2⟩ : Z₂.TotalSpace))
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) := by
    intro i₁ i₂
    -- the trivialised expression on the source chart
    have hcont : ContinuousOn (fun p : Z₁.TotalSpace =>
        (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F'))
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) := by
      have hrw : ∀ p ∈ (Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂),
          (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F')
            = (⟨f p.1, ((Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)).comp
                ((T p.1).comp (Z₁.coordChange i₁ (Z₁.indexAt p.1) p.1)))
                ((Z₁.localTriv i₁) p).2⟩ : B × F') := by
        intro p hp
        congr 1
        have hinner : ((Z₁.localTriv i₁) p).2 = Z₁.coordChange (Z₁.indexAt p.1) i₁ p.1 p.2 := by
          rw [VectorBundleCore.localTriv_apply]
        have hcomp' : (Z₁.coordChange i₁ (Z₁.indexAt p.1) p.1)
            ((Z₁.coordChange (Z₁.indexAt p.1) i₁ p.1) p.2) = p.2 := by
          have hx : p.1 ∈ Z₁.baseSet (Z₁.indexAt p.1) ∩ Z₁.baseSet i₁ :=
            ⟨Z₁.mem_baseSet_at p.1, (VectorBundleCore.mem_localTriv_source Z₁ i₁ p).mp hp.1⟩
          have h := Z₁.coordChange_comp (Z₁.indexAt p.1) i₁ (Z₁.indexAt p.1) p.1
            ⟨hx, Z₁.mem_baseSet_at p.1⟩ p.2
          rwa [Z₁.coordChange_self (Z₁.indexAt p.1) p.1 (Z₁.mem_baseSet_at p.1) p.2] at h
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hinner]
        exact congrArg (fun w => (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 w))
          hcomp'.symm
      refine ContinuousOn.congr ?_ hrw
      have h1 : ContinuousOn (fun p : Z₁.TotalSpace => f p.1)
          ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) :=
        f.continuous.comp_continuousOn
          ((FiberBundle.continuous_proj F Z₁.Fiber).continuousOn)
      have hclm : ContinuousOn (fun p : Z₁.TotalSpace =>
          (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)).comp
            ((T p.1).comp (Z₁.coordChange i₁ (Z₁.indexAt p.1) p.1)))
          ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) := by
        have hb : Set.MapsTo (fun p : Z₁.TotalSpace => p.1)
            ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂))
            (Z₁.baseSet i₁ ∩ f ⁻¹' Z₂.baseSet i₂) := fun p hp =>
          ⟨(VectorBundleCore.mem_localTriv_source Z₁ i₁ p).mp hp.1, hp.2⟩
        exact ContinuousOn.comp (hT i₁ i₂)
          (FiberBundle.continuous_proj F Z₁.Fiber).continuousOn hb
      have hsnd : ContinuousOn (fun p : Z₁.TotalSpace => ((Z₁.localTriv i₁) p).2)
          ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) :=
        (Continuous.comp_continuousOn continuous_snd (Z₁.localTriv i₁).continuousOn).mono
          (fun x hx => hx.1)
      exact ContinuousOn.prodMk h1 (hclm.clm_apply hsnd)
    -- assemble via the target trivialisation
    intro p hp
    have hmem : (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F')
        ∈ (Z₂.localTriv i₂).target := by
      rw [VectorBundleCore.mem_localTriv_target]; exact hp.2
    have hcomp : ContinuousWithinAt (fun p : Z₁.TotalSpace =>
        (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F'))
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) p :=
      hcont.continuousWithinAt hp
    let Ψ : B × F' → Z₂.TotalSpace := fun q => ⟨q.1, (Z₂.localTriv i₂).symm q.1 q.2⟩
    let Φ : Z₁.TotalSpace → B × F' := fun p =>
      (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F')
    have hsymm : ContinuousWithinAt Ψ ((Z₂.localTriv i₂).baseSet ×ˢ Set.univ) (Φ p) :=
      (Z₂.localTriv i₂).continuousOn_symm.continuousWithinAt (by
        simp only [Set.mem_prod, Set.mem_univ, and_true]; exact hp.2)
    have hfinal : ContinuousWithinAt (Ψ ∘ Φ)
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) p :=
      hsymm.comp hcomp (fun q hq =>
        (VectorBundleCore.mem_localTriv_target Z₂ i₂ (Φ q)).mpr
          (by simpa [Φ, VectorBundleCore.baseSet_at] using hq.2))
    have hpt : ∀ q ∈ (Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂),
        (⟨f q.1, T q.1 q.2⟩ : Z₂.TotalSpace) = Ψ (Φ q) := by
      intro q hq
      have hq2 : f q.1 ∈ Z₂.baseSet i₂ := hq.2
      show (⟨f q.1, T q.1 q.2⟩ : Z₂.TotalSpace)
        = (⟨f q.1, (Z₂.localTriv i₂).symm (f q.1)
        ((Z₂.coordChange (Z₂.indexAt (f q.1)) i₂ (f q.1)) (T q.1 q.2))⟩ : Z₂.TotalSpace)
      rw [VectorBundleCore.localTriv_symm_apply Z₂ i₂ hq2]
      congr 1
      have hcc := Z₂.coordChange_comp (Z₂.indexAt (f q.1)) i₂ (Z₂.indexAt (f q.1)) (f q.1)
        ⟨⟨Z₂.mem_baseSet_at (f q.1), hq2⟩, Z₂.mem_baseSet_at (f q.1)⟩ ((T q.1) q.2)
      rw [hcc, Z₂.coordChange_self (Z₂.indexAt (f q.1)) (f q.1)
        (Z₂.mem_baseSet_at (f q.1))]
    exact hfinal.congr hpt (hpt p hp)
  rw [continuous_iff_continuousAt]
  intro p
  refine (hgOn (Z₁.indexAt p.1) (Z₂.indexAt (f p.1))).continuousAt ?_
  refine (IsOpen.inter ?_ ?_).mem_nhds ⟨?_, ?_⟩
  · exact (Z₁.localTriv (Z₁.indexAt p.1)).open_source
  · exact (Z₂.isOpen_baseSet (Z₂.indexAt (f p.1))).preimage f.continuous
      |>.preimage (FiberBundle.continuous_proj F Z₁.Fiber)
  · exact (VectorBundleCore.mem_localTriv_source Z₁ (Z₁.indexAt p.1) p).mpr
      (Z₁.mem_baseSet_at p.1)
  · exact Z₂.mem_baseSet_at (f p.1)

end

end Work.Thom
