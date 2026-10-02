import Mathlib
import Submission.Work.Thom.Iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Thom

/-- Transporting the fibre of a `VectorBundleCore` along a continuous linear equivalence `e`.
If `Z` is a core with fibre `F`, this is the core with fibre `F'` whose coordinate changes are
`e ∘ Z.coordChange ∘ e⁻¹`; the two cores are canonically isomorphic (in the sense of
`Work.Thom.BundleIso`). -/
theorem exists_coreMapFibre {𝕜 : Type} [NontriviallyNormedField 𝕜] {B : Type} [TopologicalSpace B]
    {F F' : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] {ι : Type} (e : F ≃L[𝕜] F') (Z : VectorBundleCore 𝕜 B F ι) :
    ∃ Z' : VectorBundleCore 𝕜 B F' ι,
      Z'.baseSet = Z.baseSet ∧ Z'.indexAt = Z.indexAt ∧
      (∀ i j x, Z'.coordChange i j x
        = (e : F →L[𝕜] F').comp ((Z.coordChange i j x).comp (e.symm : F' →L[𝕜] F))) ∧
      Nonempty (Work.Thom.BundleIso Z Z') := by
  let Z' : VectorBundleCore 𝕜 B F' ι :=
  { baseSet := Z.baseSet
    isOpen_baseSet := Z.isOpen_baseSet
    indexAt := Z.indexAt
    mem_baseSet_at := Z.mem_baseSet_at
    coordChange := fun i j x => (e : F →L[𝕜] F').comp ((Z.coordChange i j x).comp (e.symm : F' →L[𝕜] F))
    coordChange_self := by
      intro i x hx v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      rw [Z.coordChange_self i x hx]; simp
    continuousOn_coordChange := by
      intro i j
      exact ContinuousOn.clm_comp continuousOn_const
        (ContinuousOn.clm_comp (Z.continuousOn_coordChange i j) continuousOn_const)
    coordChange_comp := by
      intro i j k x hx v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      rw [ContinuousLinearEquiv.symm_apply_apply, Z.coordChange_comp i j k x hx] }
  have hcoord : ∀ i j x, Z'.coordChange i j x
      = (e : F →L[𝕜] F').comp ((Z.coordChange i j x).comp (e.symm : F' →L[𝕜] F)) := fun i j x => rfl
  have hidx : ∀ x, Z'.indexAt x = Z.indexAt x := fun x => rfl
  -- Continuity of the map sending `⟨b, v⟩` to `⟨b, e v⟩` between the total spaces.
  have cont₁ : Continuous fun p : Z.TotalSpace => (⟨p.1, e p.2⟩ : Z'.TotalSpace) := by
    rw [continuous_iff_continuousAt]
    intro x
    refine (Z'.localTriv (Z'.indexAt x.1)).continuousAt_of_comp_left ?_ ?_ ?_
    · have : (Z'.proj ∘ (fun p : Z.TotalSpace => (⟨p.1, e p.2⟩ : Z'.TotalSpace))) = Z.proj := by
        funext p; rfl
      rw [this]; exact Z.continuous_proj.continuousAt
    · exact Z'.mem_baseSet_at x.1
    · have heq : ((Z'.localTriv (Z'.indexAt x.1)) ∘ (fun p : Z.TotalSpace => (⟨p.1, e p.2⟩ : Z'.TotalSpace)))
          = ((fun q : B × F => (⟨q.1, e q.2⟩ : B × F')) ∘ (Z.localTriv (Z.indexAt x.1))) := by
        funext p
        simp only [Function.comp_apply]
        rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply, hcoord]
        simp only [hidx, ContinuousLinearMap.comp_apply]
        apply Prod.ext
        · rfl
        · exact congrArg (fun w => (e : F →L[𝕜] F') w)
            (congrArg (Z.coordChange (Z.indexAt p.1) (Z.indexAt x.1) p.1)
              (ContinuousLinearEquiv.symm_apply_apply e (p.2 : F)))
      rw [heq]
      exact (continuous_fst.prodMk (e.continuous.comp continuous_snd)).continuousAt.comp
        ((Z.localTrivAt x.1).continuousOn.continuousAt
          ((Z.localTrivAt x.1).open_source.mem_nhds (Z.mem_source_at x.1 x.2)))
  -- Continuity of the inverse map.
  have cont₂ : Continuous fun p : Z'.TotalSpace => (⟨p.1, (e.symm : F' →L[𝕜] F) p.2⟩ : Z.TotalSpace) := by
    rw [continuous_iff_continuousAt]
    intro x
    refine (Z.localTriv (Z.indexAt x.1)).continuousAt_of_comp_left ?_ ?_ ?_
    · have : (Z.proj ∘ (fun p : Z'.TotalSpace => (⟨p.1, (e.symm : F' →L[𝕜] F) p.2⟩ : Z.TotalSpace))) = Z'.proj := by
        funext p; rfl
      rw [this]; exact Z'.continuous_proj.continuousAt
    · exact Z.mem_baseSet_at x.1
    · have heq : ((Z.localTriv (Z.indexAt x.1)) ∘ (fun p : Z'.TotalSpace => (⟨p.1, (e.symm : F' →L[𝕜] F) p.2⟩ : Z.TotalSpace)))
          = ((fun q : B × F' => (⟨q.1, (e.symm : F' →L[𝕜] F) q.2⟩ : B × F)) ∘ (Z'.localTriv (Z'.indexAt x.1))) := by
        funext p
        simp only [Function.comp_apply]
        rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply, hcoord]
        simp only [hidx]
        apply Prod.ext
        · rfl
        · exact (ContinuousLinearEquiv.symm_apply_apply e _).symm
      rw [heq]
      exact (continuous_fst.prodMk ((e.symm).continuous.comp continuous_snd)).continuousAt.comp
        ((Z'.localTrivAt x.1).continuousOn.continuousAt
          ((Z'.localTrivAt x.1).open_source.mem_nhds (Z'.mem_source_at x.1 x.2)))
  refine ⟨Z', rfl, rfl, fun i j x => rfl, ⟨?_⟩⟩
  exact
  { hom := fun b => (e : F →L[𝕜] F').toLinearMap
    inv := fun b => (e.symm : F' →L[𝕜] F).toLinearMap
    left_inv := fun b x => e.symm_apply_apply x
    right_inv := fun b y => e.apply_symm_apply y
    continuous_hom := cont₁
    continuous_inv := cont₂ }

end Work.Thom
