import Mathlib
import Submission.Work.Thom.Iso
import Submission.Work.Thom.BundleIso_comap_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {ι ι' : Type*}

/-- **Construction of a bundle isomorphism from a gauge family.**

`Φ i i' b : F →L[𝕜] F'` is the matrix of the candidate map in the source chart `i` and target chart
`i'`, and `Φinv` that of its inverse.  The identity `Z.coordChange p q` is read as "`p`-coordinates
to `q`-coordinates". -/
theorem nonempty_bundleIso_of_gauge (Z : VectorBundleCore 𝕜 B F ι)
    (Z' : VectorBundleCore 𝕜 B F' ι')
    (Φ : ι → ι' → B → (F →L[𝕜] F')) (Φinv : ι → ι' → B → (F' →L[𝕜] F))
    (hcont : ∀ i i', ContinuousOn (fun b => Φ i i' b) (Z.baseSet i ∩ Z'.baseSet i'))
    (hcontinv : ∀ i i', ContinuousOn (fun b => Φinv i i' b) (Z.baseSet i ∩ Z'.baseSet i'))
    (htgt : ∀ i t t' b, b ∈ Z.baseSet i → b ∈ Z'.baseSet t → b ∈ Z'.baseSet t' →
      (Z'.coordChange t t' b).comp (Φ i t b) = Φ i t' b)
    (hsrc : ∀ i t i' b, b ∈ Z.baseSet i → b ∈ Z.baseSet i' → b ∈ Z'.baseSet t →
      (Φ i t b).comp (Z.coordChange i' i b) = Φ i' t b)
    (htgtinv : ∀ i t t' b, b ∈ Z.baseSet i → b ∈ Z'.baseSet t → b ∈ Z'.baseSet t' →
      (Φinv i t b).comp (Z'.coordChange t' t b) = Φinv i t' b)
    (hsrcinv : ∀ i t i' b, b ∈ Z.baseSet i → b ∈ Z.baseSet i' → b ∈ Z'.baseSet t →
      (Z.coordChange i i' b).comp (Φinv i t b) = Φinv i' t b)
    (hleft : ∀ i i' b x, b ∈ Z.baseSet i ∩ Z'.baseSet i' → Φinv i i' b (Φ i i' b x) = x)
    (hright : ∀ i i' b y, b ∈ Z.baseSet i ∩ Z'.baseSet i' → Φ i i' b (Φinv i i' b y) = y) :
    Nonempty (BundleIso Z Z') := by
  have hT : ∀ i₁ i₂, ContinuousOn (fun b : B =>
      (Z'.coordChange (Z'.indexAt b) i₂ b).comp
        (((Φ (Z.indexAt b) (Z'.indexAt b) b).comp (Z.coordChange i₁ (Z.indexAt b) b))))
      (Z.baseSet i₁ ∩ Z'.baseSet i₂) := by
    intro i₁ i₂
    refine (hcont i₁ i₂).congr (fun b hb => ?_)
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp only [ContinuousLinearMap.comp_apply]
    have h1 := congrArg (fun (L : F →L[𝕜] F') => L (Z.coordChange i₁ (Z.indexAt b) b v))
        (htgt (Z.indexAt b) (Z'.indexAt b) i₂ b (Z.mem_baseSet_at b)
          (Z'.mem_baseSet_at b) hb.2)
    rw [ContinuousLinearMap.comp_apply] at h1
    rw [h1]
    have h2 := congrArg (fun (L : F →L[𝕜] F') => L v)
      (hsrc (Z.indexAt b) i₂ i₁ b (Z.mem_baseSet_at b) hb.1 hb.2)
    rwa [ContinuousLinearMap.comp_apply] at h2
  have hTi : ∀ (i₂ : ι') (i₁ : ι), ContinuousOn (fun b : B =>
      (Z.coordChange (Z.indexAt b) i₁ b).comp
        (((Φinv (Z.indexAt b) (Z'.indexAt b) b).comp (Z'.coordChange i₂ (Z'.indexAt b) b))))
      (Z'.baseSet i₂ ∩ Z.baseSet i₁) := by
    intro i₂ i₁
    refine ((hcontinv i₁ i₂).mono (fun b hb => ⟨hb.2, hb.1⟩)).congr (fun b hb => ?_)
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp only [ContinuousLinearMap.comp_apply]
    have h1 := congrArg (fun (L : F' →L[𝕜] F) => L v)
        (htgtinv (Z.indexAt b) (Z'.indexAt b) i₂ b (Z.mem_baseSet_at b)
          (Z'.mem_baseSet_at b) hb.1)
    rw [ContinuousLinearMap.comp_apply] at h1
    rw [h1]
    have h2 := congrArg (fun (L : F' →L[𝕜] F) => L v)
      (hsrcinv (Z.indexAt b) i₂ i₁ b (Z.mem_baseSet_at b) hb.2 hb.1)
    rwa [ContinuousLinearMap.comp_apply] at h2
  refine ⟨{ hom := fun b => (Φ (Z.indexAt b) (Z'.indexAt b) b).toLinearMap
            inv := fun b => (Φinv (Z.indexAt b) (Z'.indexAt b) b).toLinearMap
            left_inv := fun b x => hleft _ _ b x ⟨Z.mem_baseSet_at b, Z'.mem_baseSet_at b⟩
            right_inv := fun b y => hright _ _ b y ⟨Z.mem_baseSet_at b, Z'.mem_baseSet_at b⟩
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · exact continuous_totalSpaceMap_clm_gen Z Z'
      (ContinuousMap.id B) (fun b => Φ (Z.indexAt b) (Z'.indexAt b) b) hT
  · exact continuous_totalSpaceMap_clm_gen Z' Z
      (ContinuousMap.id B) (fun b => Φinv (Z.indexAt b) (Z'.indexAt b) b) hTi

end

end Work.Thom
