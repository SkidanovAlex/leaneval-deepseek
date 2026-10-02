import Mathlib
import Submission.Work.Thom.manifoldP1
import Submission.Work.TangentClasses.Tangent
import Submission.Work.Thom.Iso
import Submission.Work.Thom.chernClass_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Presentation independence of the Chern classes of the complexified tangent bundle

This module proves `Work.Gen.TangentPresentation`: the Chern class of the complexified tangent
bundle of a compact smooth manifold, presented over *any* finite cover extracted from the atlas,
does not depend on the cover.

The tool is the general fact that a vector bundle core reindexed along two covering families is
isomorphic to the original one (`Work.Gen.nonempty_bundleIso_reindexCore`); its proof uses only the
continuity of transition functions between *fixed* indices.  The apparent dependence of the
total-space topology on the chosen index map `indexAt` is repaired by the canonical fibrewise gauge
`W.coordChange (σ (indexAt b)) (σ' (indexAt b)) b`.
-/

open Work.TangentClasses
open Work.Thom
open Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.Gen


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {ι : Type*}

noncomputable def reindexCore (W : VectorBundleCore 𝕜 B F ι) {ι' : Type*} (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ W.baseSet (σ i)) : VectorBundleCore 𝕜 B F ι' where
  baseSet i := W.baseSet (σ i)
  isOpen_baseSet i := W.isOpen_baseSet (σ i)
  indexAt x := Classical.choose (hσ x)
  mem_baseSet_at x := Classical.choose_spec (hσ x)
  coordChange i j x := W.coordChange (σ i) (σ j) x
  coordChange_self i x hx v := W.coordChange_self (σ i) x hx v
  continuousOn_coordChange i j := W.continuousOn_coordChange (σ i) (σ j)
  coordChange_comp i j l x hx v := W.coordChange_comp (σ i) (σ j) (σ l) x hx v

@[simp] theorem reindexCore_baseSet (W : VectorBundleCore 𝕜 B F ι) {ι' : Type*}
    (σ : ι' → ι) (hσ) (i : ι') : (reindexCore W σ hσ).baseSet i = W.baseSet (σ i) := rfl
@[simp] theorem reindexCore_coordChange (W : VectorBundleCore 𝕜 B F ι) {ι' : Type*}
    (σ : ι' → ι) (hσ) (i j : ι') (x : B) :
    (reindexCore W σ hσ).coordChange i j x = W.coordChange (σ i) (σ j) x := rfl

theorem nonempty_bundleIso_reindexCore (W : VectorBundleCore 𝕜 B F ι) {ι' ι'' : Type*}
    (σ : ι' → ι) (hσ : ∀ x, ∃ i, x ∈ W.baseSet (σ i))
    (σ' : ι'' → ι) (hσ' : ∀ x, ∃ i, x ∈ W.baseSet (σ' i)) :
    Nonempty (BundleIso (reindexCore W σ hσ) (reindexCore W σ' hσ')) := by
  refine ⟨{
    hom := fun b => (W.coordChange (σ ((reindexCore W σ hσ).indexAt b))
      (σ' ((reindexCore W σ' hσ').indexAt b)) b).toLinearMap
    inv := fun b => (W.coordChange (σ' ((reindexCore W σ' hσ').indexAt b))
      (σ ((reindexCore W σ hσ).indexAt b)) b).toLinearMap
    left_inv := ?_
    right_inv := ?_
    continuous_hom := ?_
    continuous_inv := ?_ }⟩
  · intro b x
    refine (W.coordChange_comp (σ ((reindexCore W σ hσ).indexAt b))
        (σ' ((reindexCore W σ' hσ').indexAt b)) (σ ((reindexCore W σ hσ).indexAt b)) b
        ⟨⟨(reindexCore W σ hσ).mem_baseSet_at b,
          (reindexCore W σ' hσ').mem_baseSet_at b⟩,
          (reindexCore W σ hσ).mem_baseSet_at b⟩ x).trans ?_
    exact W.coordChange_self (σ ((reindexCore W σ hσ).indexAt b)) b
      ((reindexCore W σ hσ).mem_baseSet_at b) x
  · intro b y
    refine (W.coordChange_comp (σ' ((reindexCore W σ' hσ').indexAt b))
        (σ ((reindexCore W σ hσ).indexAt b)) (σ' ((reindexCore W σ' hσ').indexAt b)) b
        ⟨⟨(reindexCore W σ' hσ').mem_baseSet_at b,
          (reindexCore W σ hσ).mem_baseSet_at b⟩,
          (reindexCore W σ' hσ').mem_baseSet_at b⟩ y).trans ?_
    exact W.coordChange_self (σ' ((reindexCore W σ' hσ').indexAt b)) b
      ((reindexCore W σ' hσ').mem_baseSet_at b) y
  · rw [continuous_iff_continuousAt]; intro p₀
    set i : ι' := (reindexCore W σ hσ).indexAt p₀.1
    set i' : ι'' := (reindexCore W σ' hσ').indexAt p₀.1
    set G : B × F → B × F := fun q => (⟨q.1, W.coordChange (σ i) (σ' i') q.1 q.2⟩ : B × F)
    have hb1 : p₀.1 ∈ W.baseSet (σ i) := (reindexCore W σ hσ).mem_baseSet_at p₀.1
    have hb2 : p₀.1 ∈ W.baseSet (σ' i') := (reindexCore W σ' hσ').mem_baseSet_at p₀.1
    have hopenS : IsOpen (((W.baseSet (σ i)) ∩ (W.baseSet (σ' i'))) ×ˢ (Set.univ : Set F)) :=
      ((W.isOpen_baseSet (σ i)).inter (W.isOpen_baseSet (σ' i'))).prod isOpen_univ
    have hGOn : ContinuousOn G (((W.baseSet (σ i)) ∩ (W.baseSet (σ' i'))) ×ˢ (Set.univ : Set F)) := by
      refine continuous_fst.continuousOn.prodMk ?_
      refine ContinuousOn.clm_apply ?_ continuous_snd.continuousOn
      exact (W.continuousOn_coordChange (σ i) (σ' i')).comp continuous_fst.continuousOn
        (fun q hq => hq.1)
    have hmemS : ((reindexCore W σ hσ).localTriv i p₀)
        ∈ ((W.baseSet (σ i)) ∩ (W.baseSet (σ' i'))) ×ˢ (Set.univ : Set F) := by
      refine ⟨?_, trivial⟩
      rw [VectorBundleCore.localTriv_apply]; exact ⟨hb1, hb2⟩
    have hGcont : ContinuousAt G ((reindexCore W σ hσ).localTriv i p₀) :=
      hGOn.continuousAt (hopenS.mem_nhds hmemS)
    refine (Bundle.Trivialization.continuousAt_of_comp_left
      ((reindexCore W σ' hσ').localTriv i') ?_ ?_ ?_)
    · show ContinuousAt (fun p : (reindexCore W σ hσ).TotalSpace => p.1) p₀
      exact (reindexCore W σ hσ).continuous_proj.continuousAt
    · show p₀.1 ∈ ((reindexCore W σ' hσ').localTriv i').baseSet
      rw [← VectorBundleCore.baseSet_at (reindexCore W σ' hσ') i']; exact hb2
    · have hlopen : IsOpen ((reindexCore W σ hσ).localTriv i).source :=
        ((reindexCore W σ hσ).localTriv i).open_source
      have hmeml : p₀ ∈ ((reindexCore W σ hσ).localTriv i).source := by
        rw [VectorBundleCore.mem_localTriv_source]; exact hb1
      have hcont2 : ContinuousAt
          (fun p : (reindexCore W σ hσ).TotalSpace =>
            G ((reindexCore W σ hσ).localTriv i p)) p₀ :=
        hGcont.comp (((reindexCore W σ hσ).localTriv i).continuousOn.continuousAt
          (hlopen.mem_nhds hmeml))
      refine hcont2.congr ?_
      have hopen2 : IsOpen ((W.baseSet (σ i)) ∩ (W.baseSet (σ' i'))) :=
        (W.isOpen_baseSet (σ i)).inter (W.isOpen_baseSet (σ' i'))
      have hnhds : {b | b ∈ W.baseSet (σ i) ∧ b ∈ W.baseSet (σ' i')} ∈ 𝓝 p₀.1 :=
        hopen2.mem_nhds ⟨hb1, hb2⟩
      filter_upwards [(reindexCore W σ hσ).continuous_proj.continuousAt hnhds] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      show G ((reindexCore W σ hσ).localTriv i p)
        = ((reindexCore W σ' hσ').localTriv i')
            (⟨p.proj, W.coordChange (σ ((reindexCore W σ hσ).indexAt p.proj))
              (σ' ((reindexCore W σ' hσ').indexAt p.proj)) p.proj p.snd⟩ :
              (reindexCore W σ' hσ').TotalSpace)
      apply Prod.ext
      · rw [VectorBundleCore.localTriv_apply]
        rfl
      · have hA1 : p.proj ∈ W.baseSet (σ ((reindexCore W σ hσ).indexAt p.proj)) :=
          (reindexCore W σ hσ).mem_baseSet_at p.proj
        have hA2 : p.proj ∈ W.baseSet (σ' ((reindexCore W σ' hσ').indexAt p.proj)) :=
          (reindexCore W σ' hσ').mem_baseSet_at p.proj
        change W.coordChange (σ i) (σ' i') p.proj
            (W.coordChange (σ ((reindexCore W σ hσ).indexAt p.proj)) (σ i) p.proj p.snd)
          = W.coordChange (σ' ((reindexCore W σ' hσ').indexAt p.proj)) (σ' i') p.proj
            (W.coordChange (σ ((reindexCore W σ hσ).indexAt p.proj))
              (σ' ((reindexCore W σ' hσ').indexAt p.proj)) p.proj p.snd)
        refine (W.coordChange_comp (σ ((reindexCore W σ hσ).indexAt p.proj)) (σ i) (σ' i') p.proj
            ⟨⟨hA1, hp1⟩, hp2⟩ p.snd).trans ?_
        exact (W.coordChange_comp (σ ((reindexCore W σ hσ).indexAt p.proj))
            (σ' ((reindexCore W σ' hσ').indexAt p.proj)) (σ' i') p.proj
            ⟨⟨hA1, hA2⟩, hp2⟩ p.snd).symm
  · rw [continuous_iff_continuousAt]; intro p₀
    set i : ι' := (reindexCore W σ hσ).indexAt p₀.1
    set i' : ι'' := (reindexCore W σ' hσ').indexAt p₀.1
    set G : B × F → B × F := fun q => (⟨q.1, W.coordChange (σ' i') (σ i) q.1 q.2⟩ : B × F)
    have hb1 : p₀.1 ∈ W.baseSet (σ i) := (reindexCore W σ hσ).mem_baseSet_at p₀.1
    have hb2 : p₀.1 ∈ W.baseSet (σ' i') := (reindexCore W σ' hσ').mem_baseSet_at p₀.1
    have hopenS : IsOpen (((W.baseSet (σ' i')) ∩ (W.baseSet (σ i))) ×ˢ (Set.univ : Set F)) :=
      ((W.isOpen_baseSet (σ' i')).inter (W.isOpen_baseSet (σ i))).prod isOpen_univ
    have hGOn : ContinuousOn G (((W.baseSet (σ' i')) ∩ (W.baseSet (σ i))) ×ˢ (Set.univ : Set F)) := by
      refine continuous_fst.continuousOn.prodMk ?_
      refine ContinuousOn.clm_apply ?_ continuous_snd.continuousOn
      exact (W.continuousOn_coordChange (σ' i') (σ i)).comp continuous_fst.continuousOn
        (fun q hq => hq.1)
    have hmemS : ((reindexCore W σ' hσ').localTriv i' p₀)
        ∈ ((W.baseSet (σ' i')) ∩ (W.baseSet (σ i))) ×ˢ (Set.univ : Set F) := by
      refine ⟨?_, trivial⟩
      rw [VectorBundleCore.localTriv_apply]; exact ⟨hb2, hb1⟩
    have hGcont : ContinuousAt G ((reindexCore W σ' hσ').localTriv i' p₀) :=
      hGOn.continuousAt (hopenS.mem_nhds hmemS)
    refine (Bundle.Trivialization.continuousAt_of_comp_left
      ((reindexCore W σ hσ).localTriv i) ?_ ?_ ?_)
    · show ContinuousAt (fun p : (reindexCore W σ' hσ').TotalSpace => p.1) p₀
      exact (reindexCore W σ' hσ').continuous_proj.continuousAt
    · show p₀.1 ∈ ((reindexCore W σ hσ).localTriv i).baseSet
      rw [← VectorBundleCore.baseSet_at (reindexCore W σ hσ) i]; exact hb1
    · have hlopen : IsOpen ((reindexCore W σ' hσ').localTriv i').source :=
        ((reindexCore W σ' hσ').localTriv i').open_source
      have hmeml : p₀ ∈ ((reindexCore W σ' hσ').localTriv i').source := by
        rw [VectorBundleCore.mem_localTriv_source]; exact hb2
      have hcont2 : ContinuousAt
          (fun p : (reindexCore W σ' hσ').TotalSpace =>
            G ((reindexCore W σ' hσ').localTriv i' p)) p₀ :=
        hGcont.comp (((reindexCore W σ' hσ').localTriv i').continuousOn.continuousAt
          (hlopen.mem_nhds hmeml))
      refine hcont2.congr ?_
      have hopen2 : IsOpen ((W.baseSet (σ i)) ∩ (W.baseSet (σ' i'))) :=
        (W.isOpen_baseSet (σ i)).inter (W.isOpen_baseSet (σ' i'))
      have hnhds : {b | b ∈ W.baseSet (σ i) ∧ b ∈ W.baseSet (σ' i')} ∈ 𝓝 p₀.1 :=
        hopen2.mem_nhds ⟨hb1, hb2⟩
      filter_upwards [(reindexCore W σ' hσ').continuous_proj.continuousAt hnhds] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      show G ((reindexCore W σ' hσ').localTriv i' p)
        = ((reindexCore W σ hσ).localTriv i)
            (⟨p.proj, W.coordChange (σ' ((reindexCore W σ' hσ').indexAt p.proj))
              (σ ((reindexCore W σ hσ).indexAt p.proj)) p.proj p.snd⟩ :
              (reindexCore W σ hσ).TotalSpace)
      apply Prod.ext
      · rw [VectorBundleCore.localTriv_apply]
        rfl
      · have hA1 : p.proj ∈ W.baseSet (σ ((reindexCore W σ hσ).indexAt p.proj)) :=
          (reindexCore W σ hσ).mem_baseSet_at p.proj
        have hA2 : p.proj ∈ W.baseSet (σ' ((reindexCore W σ' hσ').indexAt p.proj)) :=
          (reindexCore W σ' hσ').mem_baseSet_at p.proj
        change W.coordChange (σ' i') (σ i) p.proj
            (W.coordChange (σ' ((reindexCore W σ' hσ').indexAt p.proj)) (σ' i') p.proj p.snd)
          = W.coordChange (σ ((reindexCore W σ hσ).indexAt p.proj)) (σ i) p.proj
            (W.coordChange (σ' ((reindexCore W σ' hσ').indexAt p.proj))
              (σ ((reindexCore W σ hσ).indexAt p.proj)) p.proj p.snd)
        refine (W.coordChange_comp (σ' ((reindexCore W σ' hσ').indexAt p.proj)) (σ' i') (σ i) p.proj
            ⟨⟨hA2, hp2⟩, hp1⟩ p.snd).trans ?_
        exact (W.coordChange_comp (σ' ((reindexCore W σ' hσ').indexAt p.proj))
            (σ ((reindexCore W σ hσ).indexAt p.proj)) (σ i) p.proj
            ⟨⟨hA2, hA1⟩, hp1⟩ p.snd).symm


/-- A **universe-polymorphic** version of `Work.Thom.complexificationCore`.  The latter is
(unnecessarily) restricted to index types in `Type 0`, while the atlas of a manifold is not;
this copy is identical field by field. -/
noncomputable def complexificationCoreUniv {B : Type*} [TopologicalSpace B] {k : ℕ} {ι : Type*}
    (Z : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k)) ι) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j b := Work.Thom.cxTrans (Z.coordChange i j b)
  coordChange_self i x hx v := by
    have h1 : Z.coordChange i i x = 1 :=
      ContinuousLinearMap.ext (fun w => Z.coordChange_self i x hx w)
    rw [h1, Work.Thom.cxTrans_one]
    rfl
  continuousOn_coordChange i j :=
    Work.Thom.continuous_cxTrans.comp_continuousOn (Z.continuousOn_coordChange i j)
  coordChange_comp i j l x hx v := by
    have hcomp : (Z.coordChange j l x).comp (Z.coordChange i j x) = Z.coordChange i l x :=
      ContinuousLinearMap.ext (fun w => Z.coordChange_comp i j l x hx w)
    rw [← hcomp, Work.Thom.cxTrans_comp, ContinuousLinearMap.comp_apply]

/-- The universe-polymorphic copy agrees with `Work.Thom.complexificationCore` after reindexing,
so it can be used in place of it. -/
theorem complexificationCoreUniv_reindex {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [FiniteDimensional ℝ E]
    {ι : Type} (σ : ι → atlas H M) (hσ : ∀ x, ∃ i, x ∈ (σ i).1.source) :
    (reindexCore
        (complexificationCoreUniv
          ((Work.TangentClasses.tangentBundle I M).mapFibre
            (Work.Thom.modelLinearEquiv (E := E)))) σ hσ)
      = Work.Thom.complexificationCore
          (((Work.TangentClasses.tangentBundle I M).mapFibre
            (Work.Thom.modelLinearEquiv (E := E))).reindex σ hσ) := rfl

/-- **Presentation independence of the Chern classes of the complexified tangent bundle.**

For a compact smooth manifold `M` and any two finite families of charts of the atlas whose sources
cover `M`, the `j`-th Chern class of the complexified tangent bundle — presented by the four-step
gluing construction `tangentBundle → mapFibre → reindex → complexificationCore` — is the same. -/
theorem TangentPresentation
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompactSpace M] [FiniteDimensional ℝ E]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (σ : ι → atlas H M) (hσ : ∀ x, ∃ i, x ∈ (σ i).1.source)
    (σ' : ι' → atlas H M) (hσ' : ∀ x, ∃ i, x ∈ (σ' i).1.source) (j : ℕ) :
    Work.Thom.chernClass (Module.finrank ℝ E) j
        (Work.Thom.complexificationCore
          (((Work.TangentClasses.tangentBundle I M).mapFibre
            (Work.Thom.modelLinearEquiv (E := E))).reindex σ hσ))
      = Work.Thom.chernClass (Module.finrank ℝ E) j
        (Work.Thom.complexificationCore
          (((Work.TangentClasses.tangentBundle I M).mapFibre
            (Work.Thom.modelLinearEquiv (E := E))).reindex σ' hσ')) := by
  obtain ⟨e⟩ := nonempty_bundleIso_reindexCore
    (complexificationCoreUniv
      ((Work.TangentClasses.tangentBundle I M).mapFibre (Work.Thom.modelLinearEquiv (E := E))))
    σ hσ σ' hσ'
  exact Work.Thom.chernClass_BundleIso _ _ e

end Work.Gen
