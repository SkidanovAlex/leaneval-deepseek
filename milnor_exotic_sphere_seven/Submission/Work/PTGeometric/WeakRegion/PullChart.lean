import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Properties

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the pullback charts of the weak region

For an ambient chart `φ` of the maximal atlas of `A` we build the *pullback chart* of `φ` to the
region `{Φ ≤ 0}`: on the points of the region with `Φ < 0` lying in the source of `φ`, it is `φ`
itself.  These charts are used to transfer submersivity from `A` to the region: at a point `m` of the
region with `m ∉ boundary Region` the region contains a neighbourhood of `m.1`, so the inclusion is
there a local diffeomorphism, and (the pullback of) the chart witnessing a submersion of `f` at `m.1`
witnesses the submersion of `f ∘ val` at `m`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners Classical

namespace Work.PTGeometric.WeakRegion

noncomputable section

namespace RegionSetupWeak

variable {k : ℕ} (S : RegionSetupWeak k)

/-! ## The pullback chart -/

/-- The source of the pullback chart of an ambient chart `φ`: the points of the region whose
underlying point lies in the source of `φ` and at which `Φ < 0`. -/
def pullSource (φ : OpenPartialHomeomorph S.A (Half k)) : Set S.Region :=
  {w : S.Region | w.1 ∈ φ.source ∧ S.Φ w.1 < 0}

/-- The target of the pullback chart of `φ`. -/
def pullTarget (φ : OpenPartialHomeomorph S.A (Half k)) : Set (Half k) :=
  φ '' {y : S.A | y ∈ φ.source ∧ S.Φ y < 0}

theorem isOpen_pullSource (φ : OpenPartialHomeomorph S.A (Half k)) :
    IsOpen (S.pullSource φ) :=
  (((φ.open_source).inter (S.hΦ.continuous.isOpen_preimage _ isOpen_Iio)).preimage
    continuous_subtype_val)

theorem pullTarget_subset_target (φ : OpenPartialHomeomorph S.A (Half k)) :
    S.pullTarget φ ⊆ φ.target := by
  rintro u ⟨y, hy, rfl⟩
  exact φ.map_source hy.1

theorem isOpen_pullTarget (φ : OpenPartialHomeomorph S.A (Half k)) :
    IsOpen (S.pullTarget φ) :=
  (φ.isOpen_image_iff_of_subset_source (fun y hy => hy.1)).mpr
    ((φ.open_source).inter (S.hΦ.continuous.isOpen_preimage _ isOpen_Iio))

/-- The ambient point underlying the inverse of the pullback chart. -/
noncomputable def pullInvVal (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    (u : Half k) : S.A :=
  if hu : u ∈ S.pullTarget φ then φ.symm u else m.1

theorem pullInvVal_of_mem (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k)) {u : Half k}
    (hu : u ∈ S.pullTarget φ) : S.pullInvVal m φ u = φ.symm u :=
  dif_pos hu

theorem pullInvVal_mem_source (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    {u : Half k} (hu : u ∈ S.pullTarget φ) : S.pullInvVal m φ u ∈ φ.source := by
  rw [S.pullInvVal_of_mem m φ hu]
  obtain ⟨y, hy, hyu⟩ := hu
  have hsymm : φ.symm u = y := by
    rw [← hyu]
    exact PartialEquiv.left_inv (φ.toPartialEquiv) hy.1
  rw [hsymm]
  exact hy.1

theorem pullInvVal_mem_neg (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    {u : Half k} (hu : u ∈ S.pullTarget φ) : S.Φ (S.pullInvVal m φ u) < 0 := by
  rw [S.pullInvVal_of_mem m φ hu]
  obtain ⟨y, hy, hyu⟩ := hu
  have hsymm : φ.symm u = y := by
    rw [← hyu]
    exact PartialEquiv.left_inv (φ.toPartialEquiv) hy.1
  rw [hsymm]
  exact hy.2

theorem pullInvVal_mem_region (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    {u : Half k} (hu : u ∈ S.pullTarget φ) : S.Φ (S.pullInvVal m φ u) ≤ 0 :=
  le_of_lt (S.pullInvVal_mem_neg m φ hu)

/-- The inverse of the pullback chart, as a `Region`-valued function. -/
noncomputable def pullInvFun (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    (u : Half k) : S.Region :=
  if hu : u ∈ S.pullTarget φ then
    (⟨S.pullInvVal m φ u, S.pullInvVal_mem_region m φ hu⟩ : S.Region)
  else m

theorem pullInvFun_of_mem (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k)) {u : Half k}
    (hu : u ∈ S.pullTarget φ) :
    S.pullInvFun m φ u
      = (⟨S.pullInvVal m φ u, S.pullInvVal_mem_region m φ hu⟩ : S.Region) :=
  dif_pos hu

theorem pullInvFun_mem_source (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    {u : Half k} (hu : u ∈ S.pullTarget φ) : S.pullInvFun m φ u ∈ S.pullSource φ := by
  rw [S.pullInvFun_of_mem m φ hu]
  exact ⟨S.pullInvVal_mem_source m φ hu, S.pullInvVal_mem_neg m φ hu⟩

/-- **The pullback chart** of an ambient chart `φ` to the region: on the points of the region where
`Φ < 0` and which lie in the source of `φ`, it is `φ` itself. -/
noncomputable def pullChart (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k)) :
    OpenPartialHomeomorph S.Region (Half k) where
  toFun w := φ w.1
  invFun := S.pullInvFun m φ
  source := S.pullSource φ
  target := S.pullTarget φ
  map_source' w hw := by
    have hw' : w.1 ∈ φ.source ∧ S.Φ w.1 < 0 := hw
    exact ⟨w.1, hw', rfl⟩
  map_target' u hu := S.pullInvFun_mem_source m φ hu
  left_inv' w hw := by
    have hw' : w.1 ∈ φ.source ∧ S.Φ w.1 < 0 := hw
    have hu : φ w.1 ∈ S.pullTarget φ := ⟨w.1, hw', rfl⟩
    have h1 : (S.pullInvFun m φ (φ w.1)).1 = S.pullInvVal m φ (φ w.1) :=
      congrArg Subtype.val (S.pullInvFun_of_mem m φ hu)
    refine Subtype.ext ?_
    rw [h1, S.pullInvVal_of_mem m φ hu]
    exact PartialEquiv.left_inv (φ.toPartialEquiv) hw'.1
  right_inv' u hu := by
    have h1 : (S.pullInvFun m φ u).1 = S.pullInvVal m φ u :=
      congrArg Subtype.val (S.pullInvFun_of_mem m φ hu)
    rw [h1, S.pullInvVal_of_mem m φ hu]
    obtain ⟨y, hy, hyu⟩ := hu
    have hsymm : φ.symm u = y := by
      rw [← hyu]
      exact PartialEquiv.left_inv (φ.toPartialEquiv) hy.1
    rw [hsymm]
    exact hyu
  open_source := S.isOpen_pullSource φ
  open_target := S.isOpen_pullTarget φ
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous (fun w : ↥(S.pullSource φ) => φ w.1.1) :=
      (φ.continuousOn_toFun).comp_continuous (by fun_prop) (fun w => w.2.1)
    have haux : (S.pullSource φ).domRestrict (fun w : S.Region => φ w.1)
        = fun w : ↥(S.pullSource φ) => φ w.1.1 := rfl
    rw [haux]
    exact h1
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have haux : (S.pullTarget φ).domRestrict (S.pullInvFun m φ)
        = fun u : ↥(S.pullTarget φ) =>
          (⟨S.pullInvVal m φ u.1, S.pullInvVal_mem_region m φ u.2⟩ : S.Region) := by
      funext u
      rw [Set.domRestrict_apply, S.pullInvFun_of_mem m φ u.2]
    rw [haux]
    refine Continuous.subtype_mk ?_ _
    rw [show (fun u : ↥(S.pullTarget φ) => S.pullInvVal m φ u.1)
        = (fun u : ↥(S.pullTarget φ) => φ.symm u.1) from
      funext fun u => S.pullInvVal_of_mem m φ u.2]
    exact (φ.continuousOn_symm.mono (S.pullTarget_subset_target φ)).comp_continuous
      (by fun_prop) (fun u => u.2)

theorem pullChart_apply_of_mem (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    {w : S.Region} (hw : w ∈ S.pullSource φ) : S.pullChart m φ w = φ w.1 := rfl

theorem pullChart_symm_apply (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    (u : Half k) : (S.pullChart m φ).symm u = S.pullInvFun m φ u := rfl

/-! ## The extended region chart on the source -/

/-- The value of the extended region chart on its source. -/
theorem chartAt_extend_apply (m : S.Region) {w : S.Region} (hw : w ∈ S.chartSource m) :
    ((S.chartAt m).extend (𝓡∂ (8 + k + 1))) w = S.chartVec m w.1 := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, S.chartAt_apply_of_mem m hw,
    modelWithCornersEuclideanHalfSpace_apply]

/-- The extended region chart at `m'`, evaluated at the inverse of the pullback chart of `φ`. -/
theorem pullChart_symm_extend_eq (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    (m' : S.Region) {z : EuclideanSpace ℝ (Fin (8 + k + 1))}
    (hz : (𝓡∂ (8 + k + 1)).symm z ∈ S.pullTarget φ)
    (hzsrc : φ.symm ((𝓡∂ (8 + k + 1)).symm z) ∈ (S.dom m').source)
    (hzT : S.domExt m' (φ.symm ((𝓡∂ (8 + k + 1)).symm z)) ∈ (S.T m').source) :
    ((S.chartAt m').extend (𝓡∂ (8 + k + 1)))
        (S.pullInvFun m φ ((𝓡∂ (8 + k + 1)).symm z))
      = S.T m' (S.domExt m' (φ.symm ((𝓡∂ (8 + k + 1)).symm z))) := by
  have h1 : (S.pullInvFun m φ ((𝓡∂ (8 + k + 1)).symm z)).1
      = φ.symm ((𝓡∂ (8 + k + 1)).symm z) :=
    (congrArg Subtype.val (S.pullInvFun_of_mem m φ hz)).trans
      (S.pullInvVal_of_mem m φ hz)
  have hmem : S.pullInvFun m φ ((𝓡∂ (8 + k + 1)).symm z) ∈ S.chartSource m' := by
    refine ⟨?_, ?_⟩
    · show (S.pullInvFun m φ ((𝓡∂ (8 + k + 1)).symm z)).1 ∈ (S.dom m').source
      rw [h1]; exact hzsrc
    · show S.domExt m' (S.pullInvFun m φ ((𝓡∂ (8 + k + 1)).symm z)).1 ∈ (S.T m').source
      rw [h1]; exact hzT
  rw [S.chartAt_extend_apply m' hmem, h1]
  rfl

/-! ## The pullback chart is a chart of the maximal atlas -/

theorem pullChart_mem_maximalAtlas (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    (hφ : φ ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A) :
    S.pullChart m φ ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.Region := by
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · have h1 : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞
        (fun w : S.Region => φ w.1) (S.pullSource φ) :=
      (contMDiffOn_of_mem_maximalAtlas hφ).comp
        ((S.contMDiffOn_val φ.source).mono (fun w hw => hw.1))
        (fun w hw => hw.1)
    exact h1.congr (fun w _ => rfl)
  · intro u hu
    set m' : S.Region := S.pullInvFun m φ u with hm'
    have hm'val : m'.1 = S.pullInvVal m φ u :=
      congrArg Subtype.val (S.pullInvFun_of_mem m φ hu)
    have hm'φ : m'.1 ∈ φ.source := by
      rw [hm'val]
      exact S.pullInvVal_mem_source m φ hu
    have hm'dom : m'.1 ∈ (S.dom m').source := S.mem_dom_source m'
    have huφtgt : u ∈ φ.target := S.pullTarget_subset_target φ hu
    have hsymm : φ.symm u = m'.1 := by
      rw [hm'val, S.pullInvVal_of_mem m φ hu]
    have hkey : φ m'.1 = u := by
      rw [← hsymm]
      exact PartialEquiv.right_inv (φ.toPartialEquiv) huφtgt
    change ContMDiffWithinAt (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞ (S.pullInvFun m φ)
      (S.pullTarget φ) u
    rw [contMDiffWithinAt_iff_of_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1))
      (I' := 𝓡∂ (8 + k + 1))
      (e := _root_.chartAt (Half k) u) (e' := S.chartAt m')
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) u)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) m')
      (mem_chart_source (Half k) u) (mem_chart_source (Half k) m')]
    refine ⟨((S.pullChart m φ).continuousOn_invFun.continuousWithinAt hu), ?_⟩
    set z₀ : EuclideanSpace ℝ (Fin (8 + k + 1)) := extChartAt (𝓡∂ (8 + k + 1)) u u with hz₀
    have hz₀I : z₀ = (𝓡∂ (8 + k + 1)) u := by rw [hz₀, extChartAt_self_apply]
    have hz₀eq : z₀ = (φ.extend (𝓡∂ (8 + k + 1))) m'.1 := by
      rw [hz₀I, OpenPartialHomeomorph.extend_coe, Function.comp_apply, hkey]
    have hz₀src : z₀ ∈ ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source := by
      rw [hz₀eq, ← OpenPartialHomeomorph.extend_image_source_inter (I := 𝓡∂ (8 + k + 1))]
      exact ⟨m'.1, ⟨hm'φ, hm'dom⟩, rfl⟩
    have hS₀nhds : ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source
        ∈ 𝓝[range (𝓡∂ (8 + k + 1))] z₀ := by
      rw [← OpenPartialHomeomorph.extend_image_source_inter (I := 𝓡∂ (8 + k + 1)), hz₀eq,
        ← OpenPartialHomeomorph.map_extend_nhds (f := φ) (I := 𝓡∂ (8 + k + 1)) hm'φ]
      exact Filter.mem_map.mpr (Filter.mem_of_superset
        (Filter.inter_mem (φ.open_source.mem_nhds hm'φ)
          ((S.dom m').open_source.mem_nhds hm'dom))
        (fun y hy => ⟨y, hy, rfl⟩))
    set G : Mod k → Mod k := fun z => S.domExt m' ((φ.extend (𝓡∂ (8 + k + 1))).symm z)
      with hGdef
    have hG : ContDiffOn ℝ ∞ G ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source :=
      contDiffOn_extendCoordChange hφ (S.dom_maximalAtlas m')
    have hF : ContDiffOn ℝ ∞ (fun z => S.T m' (G z))
        {z : Mod k | z ∈ ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source
          ∧ G z ∈ (S.T m').source} :=
      (S.T_smooth m').comp (hG.mono (fun z hz => hz.1)) (fun z hz => hz.2)
    have hz₀symm : (𝓡∂ (8 + k + 1)).symm z₀ = u := by
      rw [hz₀I]
      exact (𝓡∂ (8 + k + 1)).left_inv u
    have hcont : ContinuousAt (fun z => φ.symm ((𝓡∂ (8 + k + 1)).symm z)) z₀ := by
      have h1 : ContinuousAt (fun z : EuclideanSpace ℝ (Fin (8 + k + 1)) =>
          (𝓡∂ (8 + k + 1)).symm z) z₀ :=
        (𝓡∂ (8 + k + 1)).continuous_symm.continuousAt
      have h2 : ContinuousAt (fun y : Half k => φ.symm y) ((𝓡∂ (8 + k + 1)).symm z₀) := by
        rw [hz₀symm]
        exact φ.continuousOn_symm.continuousAt (φ.open_target.mem_nhds huφtgt)
      exact h2.comp h1
    have hpt : φ.symm ((𝓡∂ (8 + k + 1)).symm z₀) ∈ (S.dom m').source := by
      rw [hz₀symm, hsymm]
      exact hm'dom
    have hV : {z : EuclideanSpace ℝ (Fin (8 + k + 1)) |
        φ.symm ((𝓡∂ (8 + k + 1)).symm z) ∈ (S.dom m').source} ∈ 𝓝 z₀ :=
      hcont.preimage_mem_nhds ((S.dom m').open_source.mem_nhds hpt)
    have hGcont : ContinuousAt G z₀ := by
      have h3 : ContinuousAt (fun y : S.A => S.domExt m' y)
          (φ.symm ((𝓡∂ (8 + k + 1)).symm z₀)) := by
        rw [hz₀symm, hsymm]
        exact (S.dom m').continuousAt_extend hm'dom
      have h23 : ContinuousAt (fun z : EuclideanSpace ℝ (Fin (8 + k + 1)) =>
          S.domExt m' (φ.symm ((𝓡∂ (8 + k + 1)).symm z))) z₀ :=
        ContinuousAt.comp (f := fun z : EuclideanSpace ℝ (Fin (8 + k + 1)) =>
          φ.symm ((𝓡∂ (8 + k + 1)).symm z)) h3 hcont
      show ContinuousAt G z₀
      rw [hGdef]
      simpa only [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply] using h23
    have hGz₀ : G z₀ ∈ (S.T m').source := by
      have h1 : G z₀ = S.domExt m' m'.1 := by
        rw [hGdef, hz₀eq]
        exact congrArg (fun y => S.domExt m' y)
          (OpenPartialHomeomorph.extend_left_inv (f := φ) (I := 𝓡∂ (8 + k + 1)) hm'φ)
      rw [h1]
      exact S.mem_T_source m'
    have hV2 : {z : EuclideanSpace ℝ (Fin (8 + k + 1)) | G z ∈ (S.T m').source} ∈ 𝓝 z₀ :=
      hGcont.preimage_mem_nhds ((S.T m').open_source.mem_nhds hGz₀)
    have hmemH : {z : EuclideanSpace ℝ (Fin (8 + k + 1)) |
          z ∈ ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source
            ∧ G z ∈ (S.T m').source} ∈ 𝓝[range (𝓡∂ (8 + k + 1))] z₀ :=
      Filter.inter_mem hS₀nhds
        ((nhdsWithin_le_nhds (s := range (𝓡∂ (8 + k + 1))) (a := z₀)) hV2)
    have hz₀HF : z₀ ∈ {z : EuclideanSpace ℝ (Fin (8 + k + 1)) |
          z ∈ ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source
            ∧ G z ∈ (S.T m').source} := ⟨hz₀src, hGz₀⟩
    have hFct : ContDiffWithinAt ℝ ∞ (fun z => S.T m' (G z)) (range (𝓡∂ (8 + k + 1))) z₀ :=
      (hF.contDiffWithinAt hz₀HF).mono_of_mem_nhdsWithin hmemH
    have hsubT : (((_root_.chartAt (Half k) u).extend (𝓡∂ (8 + k + 1))).symm ⁻¹' S.pullTarget φ
        ∩ range (𝓡∂ (8 + k + 1))) ⊆ range (𝓡∂ (8 + k + 1)) := fun z hz => hz.2
    have hz₀T : (𝓡∂ (8 + k + 1)).symm z₀ ∈ S.pullTarget φ := by
      rw [hz₀symm]
      exact hu
    have hz₀src' : φ.symm ((𝓡∂ (8 + k + 1)).symm z₀) ∈ (S.dom m').source := by
      rw [hz₀symm, hsymm]
      exact hm'dom
    have hz₀T2' : S.domExt m' (φ.symm ((𝓡∂ (8 + k + 1)).symm z₀)) ∈ (S.T m').source := by
      rw [hz₀symm, hsymm]
      exact S.mem_T_source m'
    have hevV : ∀ᶠ z in 𝓝[(((_root_.chartAt (Half k) u).extend (𝓡∂ (8 + k + 1))).symm ⁻¹'
        S.pullTarget φ ∩ range (𝓡∂ (8 + k + 1)))] z₀,
        φ.symm ((𝓡∂ (8 + k + 1)).symm z) ∈ (S.dom m').source :=
      Filter.eventually_iff.mpr
        ((nhdsWithin_le_nhds (s := (((_root_.chartAt (Half k) u).extend (𝓡∂ (8 + k + 1))).symm ⁻¹'
          S.pullTarget φ ∩ range (𝓡∂ (8 + k + 1)))) (a := z₀)) hV)
    have hevV2 : ∀ᶠ z in 𝓝[(((_root_.chartAt (Half k) u).extend (𝓡∂ (8 + k + 1))).symm ⁻¹'
        S.pullTarget φ ∩ range (𝓡∂ (8 + k + 1)))] z₀,
        S.domExt m' (φ.symm ((𝓡∂ (8 + k + 1)).symm z)) ∈ (S.T m').source :=
      Filter.eventually_iff.mpr
        ((nhdsWithin_le_nhds (s := (((_root_.chartAt (Half k) u).extend (𝓡∂ (8 + k + 1))).symm ⁻¹'
          S.pullTarget φ ∩ range (𝓡∂ (8 + k + 1)))) (a := z₀)) hV2)
    refine (hFct.mono hsubT).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, hevV, hevV2] with z hzmem hzsrc hzT2
      exact S.pullChart_symm_extend_eq m φ m' hzmem.1 hzsrc hzT2
    · exact S.pullChart_symm_extend_eq m φ m' hz₀T hz₀src' hz₀T2'

/-! ## Submersivity transfers to the region at interior points -/

theorem isSubmersionAt_comp_val {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : S.A → F) (m : S.Region) (hm : m ∉ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (hf : IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓘(ℝ, F)) ∞ f m.1) :
    IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓘(ℝ, F)) ∞ (fun y : S.Region => f y.1) m := by
  have hnot : ¬ (m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A ∨ S.Φ m.1 = 0) := fun h =>
    hm ((S.mem_boundary_iff m).mpr h)
  have hΦ : S.Φ m.1 < 0 := lt_of_le_of_ne m.2 (fun h => hnot (Or.inr h))
  obtain ⟨Fc, instC, instS, hfc⟩ := hf
  letI : NormedAddCommGroup Fc := instC
  letI : NormedSpace ℝ Fc := instS
  refine ⟨Fc, instC, instS, ?_⟩
  refine IsSubmersionAtOfComplement.mk_of_charts (equiv := hfc.equiv)
    (domChart := S.pullChart m hfc.domChart) (codChart := hfc.codChart)
    ⟨hfc.mem_domChart_source, hΦ⟩ hfc.mem_codChart_source
    (S.pullChart_mem_maximalAtlas m hfc.domChart hfc.domChart_mem_maximalAtlas)
    hfc.codChart_mem_maximalAtlas ?_ ?_
  · intro w hw
    exact hfc.source_subset_preimage_source hw.1
  · intro z hz
    set φ := hfc.domChart with hφ
    set ψ := hfc.codChart with hψ
    have hzr : z ∈ range (𝓡∂ (8 + k + 1)) := by
      rw [← (𝓡∂ (8 + k + 1)).target_eq]
      exact hz.1
    have hzT : (𝓡∂ (8 + k + 1)).symm z ∈ S.pullTarget φ := hz.2
    have hval : S.pullInvVal m φ ((𝓡∂ (8 + k + 1)).symm z)
        = φ.symm ((𝓡∂ (8 + k + 1)).symm z) := S.pullInvVal_of_mem m φ hzT
    have harg : (((S.pullChart m φ).extend (𝓡∂ (8 + k + 1))).symm z).1
        = φ.symm ((𝓡∂ (8 + k + 1)).symm z) :=
      (congrArg Subtype.val (S.pullInvFun_of_mem m φ hzT)).trans hval
    have hz' : z ∈ (φ.extend (𝓡∂ (8 + k + 1))).target := by
      rw [OpenPartialHomeomorph.extend_target]
      exact ⟨S.pullTarget_subset_target φ hzT, hzr⟩
    have h5 := hfc.writtenInCharts hz'
    rw [Function.comp_apply, Function.comp_apply] at h5
    rw [Function.comp_apply, Function.comp_apply]
    rw [← h5, harg]
    rfl

end RegionSetupWeak

end

end Work.PTGeometric.WeakRegion
