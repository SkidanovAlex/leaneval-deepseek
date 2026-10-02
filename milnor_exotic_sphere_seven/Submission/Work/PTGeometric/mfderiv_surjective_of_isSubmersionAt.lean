import Mathlib
import Submission.Work.PTGeometric.surjective_fderivWithin_extendCoordChange
import Submission.Work.PTGeometric.surjective_fderiv_symm_of_contDiffOn

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- `writtenInExtChartAt` for a self model on the target: it is `f ∘ (extChartAt I x).symm`. -/
lemma writtenInExtChartAt_self_mod
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {k : ℕ} {f : M → EuclideanSpace ℝ (Fin k)} {x : M} :
    writtenInExtChartAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) x f =
      fun z : E => f ((extChartAt I x).symm z) := by
  funext z
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [extChartAt_self_eq]
  rfl

theorem mfderiv_surjective_of_isSubmersionAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {k : ℕ}
    {f : M → EuclideanSpace ℝ (Fin k)} {x : M}
    (h : Manifold.IsSubmersionAt I
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞) f x) :
    Function.Surjective
      (mfderiv I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) f x) := by
  classical
  have hmd : MDifferentiableAt I (𝓡 k) f x := h.contMDiffAt.mdifferentiableAt (by simp)
  obtain ⟨F, hFadd, hFmod, h'⟩ := h
  letI : NormedAddCommGroup F := hFadd
  letI : NormedSpace ℝ F := hFmod
  -- ### key objects
  let z₀ : E := (extChartAt I x) x
  let κ : PartialEquiv E E := I.extendCoordChange (chartAt H x) h'.domChart
  let A : E →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) F).comp
      ((h'.equiv : E ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × F)) : E →L[ℝ] _)
  let K : E →L[ℝ] E := fderivWithin ℝ (⇑κ) (range ⇑I) z₀
  let y : EuclideanSpace ℝ (Fin k) := A (⇑κ z₀)
  let ψe := h'.codChart.extend (𝓡 k)
  let L3 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) := fderiv ℝ (⇑ψe.symm) y
  let L : E →L[ℝ] EuclideanSpace ℝ (Fin k) := L3.comp (A.comp K)
  have hψe_src : ψe.source = h'.codChart.source := OpenPartialHomeomorph.extend_source _
  -- ### (1) facts about `z₀`
  have hz₀src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source]; exact mem_chart_source H x
  have hz₀mem : z₀ ∈ (extChartAt I x).target := (extChartAt I x).map_source hz₀src
  have hz₀range : z₀ ∈ range ⇑I := extChartAt_target_subset_range (I := I) x hz₀mem
  have hz₀uniq : UniqueDiffWithinAt ℝ (range ⇑I) z₀ :=
    (ModelWithCorners.uniqueDiffOn I).uniqueDiffWithinAt hz₀range
  have hExsymm : ⇑(extChartAt I x).symm z₀ = x := (extChartAt I x).left_inv hz₀src
  -- ### (2) facts about the coordinate change `κ`
  have hκz₀ : z₀ ∈ κ.source := by
    have hmem : ⇑(extChartAt I x) x ∈ (I.extendCoordChange (chartAt H x) h'.domChart).source := by
      rw [← OpenPartialHomeomorph.extend_image_source_inter (chartAt H x) h'.domChart (I := I)]
      exact mem_image_of_mem _ ⟨mem_chart_source H x, h'.mem_domChart_source⟩
    exact hmem
  have hκnhds : κ.source ∈ 𝓝[range ⇑I] z₀ :=
    ModelWithCorners.extendCoordChange_source_mem_nhdsWithin' (I := I) (e := chartAt H x)
      (e' := h'.domChart) (mem_chart_source H x) h'.mem_domChart_source
  have hκcd : ContDiffWithinAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (⇑κ) (range ⇑I) z₀ :=
    ModelWithCorners.contDiffWithinAt_extendCoordChange' (I := I)
      (IsManifold.chart_mem_maximalAtlas (I := I) x) h'.domChart_mem_maximalAtlas
      (mem_chart_source H x) h'.mem_domChart_source
  have hκder : HasFDerivWithinAt (⇑κ) K (range ⇑I) z₀ :=
    (hκcd.differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hKsurj : Function.Surjective K :=
    surjective_fderivWithin_extendCoordChange (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (by simp) (e := chartAt H x) (e' := h'.domChart)
      (IsManifold.chart_mem_maximalAtlas (I := I) x) h'.domChart_mem_maximalAtlas
      (mem_chart_source H x) h'.mem_domChart_source
  -- ### (3) `A` is surjective
  have hAsurj : Function.Surjective A := by
    intro w
    refine ⟨(h'.equiv.symm : (EuclideanSpace ℝ (Fin k) × F) →L[ℝ] E) (w, 0), ?_⟩
    show (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) F)
      ((h'.equiv : E →L[ℝ] (EuclideanSpace ℝ (Fin k) × F))
        ((h'.equiv.symm : (EuclideanSpace ℝ (Fin k) × F) →L[ℝ] E) (w, 0))) = w
    exact (congrArg (fun z => (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) F) z)
      (ContinuousLinearEquiv.apply_symm_apply h'.equiv (w, 0))).trans rfl
  -- ### (4) smoothness of `ψe` and of `ψe.symm`
  have hψe_sm : ContMDiffOn (𝓡 k) (𝓡 k) (((⊤ : ℕ∞) : WithTop ℕ∞))
      (⇑ψe) h'.codChart.source :=
    OpenPartialHomeomorph.contMDiffOn_extend (I := 𝓡 k) h'.codChart_mem_maximalAtlas
  have hψe_tgt : ψe.target = h'.codChart.target := by
    rw [OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe, image_id]
  have hψe_symm_sm : ContMDiffOn (𝓡 k) (𝓡 k) (((⊤ : ℕ∞) : WithTop ℕ∞))
      (⇑ψe.symm) ((𝓡 k) '' h'.codChart.target) :=
    contMDiffOn_extend_symm (I := 𝓡 k) h'.codChart_mem_maximalAtlas
  have hw : f x ∈ h'.codChart.source := h'.mem_codChart_source
  -- ### (5) the value `⇑ψe (f x)` equals `y`
  have hy_eq : ⇑ψe (f x) = y := by
    have hφex_tgt : ⇑(h'.domChart.extend I) x ∈ (h'.domChart.extend I).target :=
      (h'.domChart.extend I).map_source
        (by rw [OpenPartialHomeomorph.extend_source]; exact h'.mem_domChart_source)
    have h1 := h'.writtenInCharts hφex_tgt
    simp only [Function.comp_apply] at h1
    rw [OpenPartialHomeomorph.extend_left_inv h'.domChart h'.mem_domChart_source] at h1
    have hA_apply : ∀ v : E, A v = (h'.equiv v).1 := fun v => rfl
    have h3 : ⇑κ z₀ = ⇑(h'.domChart.extend I) x := by
      simp only [κ]
      rw [PartialEquiv.trans_apply]
      exact congrArg (⇑(h'.domChart.extend I)) hExsymm
    rw [← h3] at h1
    exact h1.trans (hA_apply (⇑κ z₀)).symm
  have hy_mem : y ∈ h'.codChart.target := by
    have hmem : ⇑ψe (f x) ∈ ψe.target := ψe.map_source (by rw [hψe_src]; exact hw)
    rwa [hy_eq, hψe_tgt] at hmem
  -- ### (6) the derivative of `ψe.symm` at `y`
  have hψ3 : HasFDerivAt (⇑ψe.symm) L3 y := by
    have hcd : ContMDiffAt (𝓡 k) (𝓡 k) (((⊤ : ℕ∞) : WithTop ℕ∞)) (⇑ψe.symm) y :=
      hψe_symm_sm.contMDiffAt (by
        rw [modelWithCornersSelf_coe, image_id]
        exact h'.codChart.open_target.mem_nhds hy_mem)
    exact ((contMDiffAt_iff_contDiffAt.mp hcd).differentiableAt (by simp)).hasFDerivAt
  -- ### (7) the derivative of `ψe` at `f x`
  have hψ2 : HasFDerivAt (⇑ψe) (fderiv ℝ (⇑ψe) (f x)) (f x) := by
    have hcd : ContMDiffAt (𝓡 k) (𝓡 k) (((⊤ : ℕ∞) : WithTop ℕ∞)) (⇑ψe) (f x) :=
      hψe_sm.contMDiffAt (h'.codChart.open_source.mem_nhds hw)
    exact ((contMDiffAt_iff_contDiffAt.mp hcd).differentiableAt (by simp)).hasFDerivAt
  -- ### (8) `L3 ∘ (fderiv ψe (f x)) = id`, hence `L3` is surjective
  have hcomp : L3.comp (fderiv ℝ (⇑ψe) (f x)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) := by
    have h3' : HasFDerivAt (⇑ψe.symm) L3 (⇑ψe (f x)) := by
      rw [hy_eq]; exact hψ3
    have hchain := h3'.comp (f x) hψ2
    have hev : (⇑ψe.symm ∘ ⇑ψe) =ᶠ[𝓝 (f x)] id := by
      have hmem : ψe.source ∈ 𝓝 (f x) := by
        rw [hψe_src]; exact h'.codChart.open_source.mem_nhds hw
      filter_upwards [hmem] with z hz
      simpa only [Function.comp_apply, id_eq] using PartialEquiv.left_inv ψe hz
    have h1 : fderiv ℝ (⇑ψe.symm ∘ ⇑ψe) (f x) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) := by
      rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_id]
    rw [hchain.fderiv] at h1
    exact h1
  have hL3surj : Function.Surjective L3 := by
    intro v
    refine ⟨(fderiv ℝ (⇑ψe) (f x)) v, ?_⟩
    have hv := congrArg
      (fun (T : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) => T v) hcomp
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hv
  -- ### (9) chain rule for the written-in-chart map
  have hAder : HasFDerivWithinAt (fun z : E => A (⇑κ z)) (A.comp K) (range ⇑I) z₀ :=
    (A.hasFDerivAt (x := ⇑κ z₀)).comp_hasFDerivWithinAt z₀ hκder
  have hGder : HasFDerivWithinAt
      (fun z : E => ⇑ψe.symm (A (⇑κ z))) L (range ⇑I) z₀ := by
    have h := hψ3.comp_hasFDerivWithinAt z₀ hAder
    exact h
  -- ### (10) eventual equality of the two expressions
  have hS : {z : E | ⇑(extChartAt I x).symm z ∈ h'.domChart.source} ∈ 𝓝[range ⇑I] z₀ := by
    have hcont : ContinuousAt (⇑(extChartAt I x).symm) z₀ :=
      OpenPartialHomeomorph.continuousAt_extend_symm' (chartAt H x) (I := I) hz₀mem
    have hpt : ⇑(extChartAt I x).symm z₀ ∈ h'.domChart.source := by
      rw [hExsymm]; exact h'.mem_domChart_source
    exact mem_nhdsWithin_of_mem_nhds
      (hcont.preimage_mem_nhds (h'.domChart.open_source.mem_nhds hpt))
  have key : ∀ z : E, ⇑(extChartAt I x).symm z ∈ h'.domChart.source →
      f (⇑(extChartAt I x).symm z) = ⇑ψe.symm (A (⇑κ z)) := by
    intro z hz
    have hκz : ⇑κ z = ⇑(h'.domChart.extend I) (⇑(extChartAt I x).symm z) := by
      simp only [κ]
      rw [PartialEquiv.trans_apply]
      rfl
    have hφsymm : ⇑(h'.domChart.extend I).symm (⇑κ z) = ⇑(extChartAt I x).symm z := by
      rw [hκz]
      exact OpenPartialHomeomorph.extend_left_inv h'.domChart hz
    have hκtgt : ⇑κ z ∈ (h'.domChart.extend I).target := by
      rw [hκz]
      exact (h'.domChart.extend I).map_source
        (by rw [OpenPartialHomeomorph.extend_source]; exact hz)
    have hw1 := h'.writtenInCharts hκtgt
    simp only [Function.comp_apply] at hw1
    rw [hφsymm] at hw1
    have hfmem : f (⇑(extChartAt I x).symm z) ∈ h'.codChart.source :=
      h'.source_subset_preimage_source hz
    have hleft := OpenPartialHomeomorph.extend_left_inv (I := 𝓡 k) h'.codChart hfmem
    rw [hw1] at hleft
    exact hleft.symm
  have heq : (fun z : E => f (⇑(extChartAt I x).symm z)) =ᶠ[𝓝[range ⇑I] z₀]
      (fun z : E => ⇑ψe.symm (A (⇑κ z))) := by
    filter_upwards [hS] with z hz
    exact key z hz
  have heq₀ : f (⇑(extChartAt I x).symm z₀) = ⇑ψe.symm (A (⇑κ z₀)) :=
    key z₀ (by rw [hExsymm]; exact h'.mem_domChart_source)
  -- ### (11) conclude
  have hwritten : writtenInExtChartAt I (𝓡 k) x f =
      fun z : E => f (⇑(extChartAt I x).symm z) := writtenInExtChartAt_self_mod I
  have hwritten_der : HasFDerivWithinAt (writtenInExtChartAt I (𝓡 k) x f) L (range ⇑I) z₀ := by
    rw [hwritten]
    exact hGder.congr_of_eventuallyEq heq heq₀
  have hmfderiv : mfderiv I (𝓡 k) f x = L := by
    rw [hmd.mfderiv]
    exact hwritten_der.fderivWithin hz₀uniq
  change Function.Surjective
    (⇑(mfderiv I (𝓡 k) f x : E →L[ℝ] EuclideanSpace ℝ (Fin k)))
  rw [hmfderiv]
  intro v
  obtain ⟨u₁, hu₁⟩ := hAsurj ((fderiv ℝ (⇑ψe) (f x)) v)
  obtain ⟨w, hw⟩ := hKsurj u₁
  refine ⟨w, ?_⟩
  have hcompv : L3 ((fderiv ℝ (⇑ψe) (f x)) v) = v := by
    have hv := congrArg
      (fun (T : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) => T v) hcomp
    exact hv
  change L3 (A (K w)) = v
  rw [hw, hu₁]
  exact hcompv

end

end Work.PTGeometric
