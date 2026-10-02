import Mathlib
import Submission.Work.Thom.Iso
import Submission.Work.Thom.BundleIso_comap_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# A bundle isomorphism from a one-sided matching of the transition functions

`X`, `Y` are two gluing-data bundles over a common base, with fibres `F`, `F'` (the *model* fibres:
`X.Fiber b` is definitionally `F`), and `e : F ≃L[𝕜] F'` is a continuous linear equivalence.

Suppose that the cover of `Y` refines that of `X` through a map `τ : ι' → ι` (`hbase`), and that
`e` conjugates the transition function of `X` from its *preferred* chart `X.indexAt b` to the chart
`τ i'` into the transition function of `Y` from its preferred chart `Y.indexAt b` to `i'`
(`hconj`; the hypothesis `b ∈ Y.baseSet i'` is what makes both charts genuine near `b`).

Then the constant fibrewise map `e` is a bundle isomorphism `X ≅ Y`: both total-space maps
`p ↦ ⟨p.1, e p.2⟩` and `p ↦ ⟨p.1, e.symm p.2⟩` are continuous.  The proof uses the criterion
`Work.Thom.continuous_totalSpaceMap_clm_gen`, which reduces the continuity to the continuity, on
`X.baseSet i₁ ∩ Y.baseSet i₂`, of the chart expression
`b ↦ Y.coordChange (Y.indexAt b) i₂ b ∘ e ∘ X.coordChange i₁ (X.indexAt b) b`; the cocycle
identities of `X` and `Y` and `hconj` rewrite this as the *fixed-index* expression
`e ∘ X.coordChange i₁ (τ i₂) b` (respectively `X.coordChange (τ i₂) i₁ b ∘ e.symm` for the
inverse), which is continuous by `VectorBundleCore.continuousOn_coordChange`.
-/

namespace Work.Gen

open Work.TangentClasses

noncomputable section

theorem cle_symm_apply_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F F' : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (e : F ≃L[𝕜] F') (x : F) : (e.symm : F' →L[𝕜] F) ((e : F →L[𝕜] F') x) = x :=
  e.symm_apply_apply x

theorem cle_apply_symm_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F F' : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (e : F ≃L[𝕜] F') (y : F') : (e : F →L[𝕜] F') ((e.symm : F' →L[𝕜] F) y) = y :=
  e.apply_symm_apply y

theorem nonempty_bundleIso_of_oneSidedMatch {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B] {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {ι ι' : Type*}
    (X : VectorBundleCore 𝕜 B F ι) (Y : VectorBundleCore 𝕜 B F' ι') (e : F ≃L[𝕜] F')
    (τ : ι' → ι)
    (hbase : ∀ i', Y.baseSet i' ⊆ X.baseSet (τ i'))
    (hconj : ∀ (i' : ι') (b : B), b ∈ Y.baseSet i' →
      (X.coordChange (X.indexAt b) (τ i') b).comp (e.symm : F' →L[𝕜] F)
        = (e.symm : F' →L[𝕜] F).comp (Y.coordChange (Y.indexAt b) i' b)) :
    Nonempty (Work.Thom.BundleIso X Y) := by
  -- `Y`'s transition in the preferred chart, expressed through `X`'s.
  have hY : ∀ (i' : ι') (b : B) (hb : b ∈ Y.baseSet i'),
      Y.coordChange (Y.indexAt b) i' b
        = (e : F →L[𝕜] F').comp ((X.coordChange (X.indexAt b) (τ i') b).comp
            (e.symm : F' →L[𝕜] F)) := by
    intro i' b hb
    apply ContinuousLinearMap.ext
    intro v
    show Y.coordChange (Y.indexAt b) i' b v
      = (e : F →L[𝕜] F') ((X.coordChange (X.indexAt b) (τ i') b) ((e.symm : F' →L[𝕜] F) v))
    rw [← cle_apply_symm_apply e (Y.coordChange (Y.indexAt b) i' b v)]
    congr 1
    rw [← ContinuousLinearMap.comp_apply, ← hconj i' b hb, ContinuousLinearMap.comp_apply]
  have hT : ∀ (i₁ : ι) (i₂ : ι'), ContinuousOn (fun b : B =>
      (Y.coordChange (Y.indexAt b) i₂ b).comp ((e : F →L[𝕜] F').comp
        (X.coordChange i₁ (X.indexAt b) b))) (X.baseSet i₁ ∩ Y.baseSet i₂) := by
    intro i₁ i₂
    refine ContinuousOn.congr (f := fun b : B =>
      (e : F →L[𝕜] F').comp (X.coordChange i₁ (τ i₂) b)) ?_ ?_
    · refine ContinuousOn.clm_comp continuousOn_const ?_
      exact (X.continuousOn_coordChange i₁ (τ i₂)).mono (fun b hb => ⟨hb.1, hbase i₂ hb.2⟩)
    · intro b hb
      have hb1 : b ∈ X.baseSet i₁ := hb.1
      have hb2 : b ∈ Y.baseSet i₂ := hb.2
      have hX2 : b ∈ X.baseSet (X.indexAt b) := X.mem_baseSet_at b
      have hX3 : b ∈ X.baseSet (τ i₂) := hbase i₂ hb2
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply]
      rw [hY i₂ b hb2]
      simp only [ContinuousLinearMap.comp_apply]
      rw [cle_symm_apply_apply,
        X.coordChange_comp i₁ (X.indexAt b) (τ i₂) b ⟨⟨hb1, hX2⟩, hX3⟩ v]
  have hTi : ∀ (i₂ : ι') (i₁ : ι), ContinuousOn (fun b : B =>
      (X.coordChange (X.indexAt b) i₁ b).comp ((e.symm : F' →L[𝕜] F).comp
        (Y.coordChange i₂ (Y.indexAt b) b))) (Y.baseSet i₂ ∩ X.baseSet i₁) := by
    intro i₂ i₁
    refine ContinuousOn.congr (f := fun b : B =>
      (X.coordChange (τ i₂) i₁ b).comp (e.symm : F' →L[𝕜] F)) ?_ ?_
    · refine ContinuousOn.clm_comp ?_ continuousOn_const
      exact (X.continuousOn_coordChange (τ i₂) i₁).mono (fun b hb => ⟨hbase i₂ hb.1, hb.2⟩)
    · intro b hb
      have hb2 : b ∈ Y.baseSet i₂ := hb.1
      have hX1 : b ∈ X.baseSet i₁ := hb.2
      have hX2 : b ∈ X.baseSet (X.indexAt b) := X.mem_baseSet_at b
      have hX3 : b ∈ X.baseSet (τ i₂) := hbase i₂ hb2
      have hY1 : b ∈ Y.baseSet (Y.indexAt b) := Y.mem_baseSet_at b
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply]
      rw [← X.coordChange_comp (X.indexAt b) (τ i₂) i₁ b ⟨⟨hX2, hX3⟩, hX1⟩
        ((e.symm : F' →L[𝕜] F) (Y.coordChange i₂ (Y.indexAt b) b v))]
      congr 1
      rw [← ContinuousLinearMap.comp_apply, hconj i₂ b hb2, ContinuousLinearMap.comp_apply,
        Y.coordChange_comp i₂ (Y.indexAt b) i₂ b ⟨⟨hb2, hY1⟩, hb2⟩ v,
        Y.coordChange_self i₂ b hb2 v]
  have hc := Work.Thom.continuous_totalSpaceMap_clm_gen X Y (ContinuousMap.id B)
    (fun _ => (e : F →L[𝕜] F')) hT
  have hci := Work.Thom.continuous_totalSpaceMap_clm_gen Y X (ContinuousMap.id B)
    (fun _ => (e.symm : F' →L[𝕜] F)) hTi
  refine ⟨{ hom := fun b => (e : F →L[𝕜] F').toLinearMap
            inv := fun b => (e.symm : F' →L[𝕜] F).toLinearMap
            left_inv := fun b x => e.symm_apply_apply x
            right_inv := fun b y => e.apply_symm_apply y
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · refine hc.congr fun p => ?_
    apply Bundle.TotalSpace.ext
    · rfl
    · rfl
  · refine hci.congr fun p => ?_
    apply Bundle.TotalSpace.ext
    · rfl
    · rfl

end

end Work.Gen
