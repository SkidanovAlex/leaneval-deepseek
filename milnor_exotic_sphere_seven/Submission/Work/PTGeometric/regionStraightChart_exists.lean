import Mathlib
import Submission.Work.PTGeometric.SourceRegionSetupBasic
import Submission.Work.PTGeometric.RegionStraightAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners Classical

namespace Work.PTGeometric

noncomputable section

variable {k : ℕ}

/-! ## Smoothness of the straightening chart -/

/-- **The straightening chart of the region is smooth on its source.** -/
theorem contMDiffOn_regionChart_toFun {S : WeakRegion.RegionSetupWeak k}
    {φ : OpenPartialHomeomorph S.A (Half k)} {ψ : Mod k → ℝ} {V : Set (Mod k)}
    (hφ : φ ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A) (hV : IsOpen V)
    (hepi : ∀ (z : Mod k), z ∈ V → ∀ (hz : 0 ≤ z.ofLp 0),
      (S.Φ (φ.symm ⟨z, hz⟩) ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0))
    (hψnn : ∀ u : Mod k, 0 ≤ ψ u)
    (hψsm : ContDiffOn ℝ ∞ (fun z : Mod k => ψ (tailVec z)) V)
    (x : S.Region) (hxsrc : x.1 ∈ φ.source) (hxV : (φ x.1).1 ∈ V) :
    ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞
      (regionChart S φ ψ V hV hepi hψnn hψsm x hxsrc hxV) (chartSrc S φ V) := by
  have hstrAux : ContDiffOn ℝ ∞ (fun z : Mod k => strAux ψ z) V := strAux_smoothOn ψ hV hψsm
  have hval : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞
      (fun w : S.Region => (w.1 : S.A)) (chartSrc S φ V) :=
    (S.contMDiffOn_val φ.source).mono (fun w hw => hw.1)
  have h1 : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞
      (fun w : S.Region => φ w.1) (chartSrc S φ V) :=
    (contMDiffOn_of_mem_maximalAtlas hφ).comp hval (fun w hw => hw.1)
  have hI : ContMDiffOn (𝓡∂ (8 + k + 1)) 𝓘(ℝ, Mod k) ∞
      (↑(𝓡∂ (8 + k + 1)) : Half k → Mod k) Set.univ :=
    (ModelWithCorners.contMDiff (𝓡∂ (8 + k + 1))).contMDiffOn
  have h2 : ContMDiffOn (𝓡∂ (8 + k + 1)) 𝓘(ℝ, Mod k) ∞
      (fun w : S.Region => (φ w.1).1) (chartSrc S φ V) :=
    hI.comp h1 (fun w _ => trivial)
  have h3 : ContMDiffOn (𝓡∂ (8 + k + 1)) 𝓘(ℝ, Mod k) ∞
      (fun w : S.Region => strAux ψ (φ w.1).1) (chartSrc S φ V) :=
    (contMDiffOn_iff_contDiffOn.mpr hstrAux).comp h2 (fun w hw => hw.2)
  have h4 : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞
      (fun w : S.Region => (𝓡∂ (8 + k + 1)).symm (strAux ψ (φ w.1).1))
      (chartSrc S φ V) :=
    (ModelWithCorners.contMDiffOn_symm (𝓡∂ (8 + k + 1))).comp h3 (fun w hw => by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact chartSrc_nonneg (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hw)
  refine h4.congr fun w hw => ?_
  rw [regionChart_apply_of_mem (hw := hw)]
  rw [modelWithCorners_halfSpace_symm_eq (n := 8 + k + 1)
    (chartSrc_nonneg (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hw)]

/-- **The inverse of the straightening chart is smooth on its target.** -/
theorem contMDiffOn_regionChart_symm {S : WeakRegion.RegionSetupWeak k}
    {φ : OpenPartialHomeomorph S.A (Half k)} {ψ : Mod k → ℝ} {V : Set (Mod k)}
    (hφ : φ ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A) (hV : IsOpen V)
    (hepi : ∀ (z : Mod k), z ∈ V → ∀ (hz : 0 ≤ z.ofLp 0),
      (S.Φ (φ.symm ⟨z, hz⟩) ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0))
    (hψnn : ∀ u : Mod k, 0 ≤ ψ u)
    (hψsm : ContDiffOn ℝ ∞ (fun z : Mod k => ψ (tailVec z)) V)
    (x : S.Region) (hxsrc : x.1 ∈ φ.source) (hxV : (φ x.1).1 ∈ V) :
    ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞
      (regionChart S φ ψ V hV hepi hψnn hψsm x hxsrc hxV).symm (chartTgt S φ ψ V) := by
  intro u₀ hu₀
  set e : OpenPartialHomeomorph S.Region (Half k) :=
    regionChart S φ ψ V hV hepi hψnn hψsm x hxsrc hxV with he
  have hsymmval : e.symm u₀
      = (⟨φ.symm (⟨unstrAux ψ u₀.1, unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u₀)⟩ : Half k),
          chartTgt_mem_region (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hψnn hu₀⟩ : S.Region) := by
    rw [he]
    exact regionChart_symm_apply_of_mem (S := S) (φ := φ) (ψ := ψ) (V := V)
      (hV := hV) (hepi := hepi) (hψnn := hψnn) (hψsm := hψsm) (hxsrc := hxsrc) (hxV := hxV) hu₀
  set w₀ : S.Region := e.symm u₀ with hw₀
  have hs : (⟨unstrAux ψ u₀.1,
      unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u₀)⟩ : Half k) ∈ φ.target :=
    half_ext_choose hu₀.2 (unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u₀))
  have hw₀val : w₀.1 = φ.symm (⟨unstrAux ψ u₀.1,
      unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u₀)⟩ : Half k) := by
    rw [hw₀]
    exact congrArg Subtype.val hsymmval
  have hw₀src : w₀.1 ∈ φ.source := by
    rw [hw₀val]
    exact φ.map_target hs
  have hu₀range : u₀.1 ∈ Set.range (𝓡∂ (8 + k + 1)) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact u₀.2
  have hmemφ : (𝓡∂ (8 + k + 1)).symm (unstrAux ψ u₀.1) ∈ φ.target := by
    rw [modelWithCorners_halfSpace_symm_eq (n := 8 + k + 1)
      (unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u₀))]
    exact hs
  have hunsAt : ContDiffAt ℝ ∞ (fun v : Mod k => unstrAux ψ v) u₀.1 :=
    (contDiffOn_unstrAux_satSet hV hψsm).contDiffAt
      ((isOpen_satSet hV).mem_nhds (subset_chartTgt_satSet hu₀))
  -- ## the chart criterion at `u₀`
  rw [contMDiffWithinAt_iff_of_mem_source (x := u₀) (y := w₀) (x' := u₀) (f := e.symm)
    (s := chartTgt S φ ψ V) (mem_chart_source (Half k) u₀) (S.mem_chartSource_self w₀)]
  refine ⟨e.continuousOn_invFun.continuousWithinAt hu₀, ?_⟩
  -- ## the sets and the two expressions
  set T : Set (Mod k) := (extChartAt (𝓡∂ (8 + k + 1)) u₀).symm ⁻¹' chartTgt S φ ψ V
    ∩ Set.range (𝓡∂ (8 + k + 1)) with hT
  set Loc : Mod k → Mod k := fun v =>
    (extChartAt (𝓡∂ (8 + k + 1)) w₀) (e.symm ((extChartAt (𝓡∂ (8 + k + 1)) u₀).symm v)) with hLoc
  set g : Mod k → S.A := fun v => φ.symm ((𝓡∂ (8 + k + 1)).symm (unstrAux ψ v)) with hg
  set Loc' : Mod k → Mod k := fun v => S.chartVec w₀ (g v) with hLoc'
  set W : Set S.A := (S.dom w₀).source ∩ (fun a : S.A => S.domExt w₀ a) ⁻¹' (S.T w₀).source
    with hW
  set N₁ : Set (Mod k) := (Set.range (𝓡∂ (8 + k + 1))
      ∩ (fun v : Mod k => (𝓡∂ (8 + k + 1)).symm (unstrAux ψ v)) ⁻¹' φ.target)
      ∩ g ⁻¹' W with hN₁
  set M₁ : Set (Mod k) := N₁ ∩ satSet V with hM₁
  have hWopen : IsOpen W := by
    have h := (S.dom w₀).continuousOn_extend.isOpen_inter_preimage
      (show IsOpen ((S.dom w₀).extend (𝓡∂ (8 + k + 1))).source from by
        rw [OpenPartialHomeomorph.extend_source]; exact (S.dom w₀).open_source)
      (S.T w₀).open_source
    simpa only [hW, OpenPartialHomeomorph.extend_source] using h
  have hgu₀ : g u₀.1 = w₀.1 := by
    rw [hg]
    show φ.symm ((𝓡∂ (8 + k + 1)).symm (unstrAux ψ u₀.1)) = w₀.1
    rw [modelWithCorners_halfSpace_symm_eq (n := 8 + k + 1)
      (unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u₀)), hw₀val]
  have hgW : g u₀.1 ∈ W := by
    rw [hgu₀]
    exact ⟨S.mem_dom_source w₀, S.mem_T_source w₀⟩
  have hu₀N₁ : u₀.1 ∈ N₁ := ⟨⟨hu₀range, hmemφ⟩, hgW⟩
  have hu₀M₁ : u₀.1 ∈ M₁ := ⟨hu₀N₁, subset_chartTgt_satSet hu₀⟩
  -- ## smoothness of the model-level expression
  have hunsSat : ContMDiffOn 𝓘(ℝ, Mod k) 𝓘(ℝ, Mod k) ∞
      (fun v : Mod k => unstrAux ψ v) (satSet V) :=
    contMDiffOn_iff_contDiffOn.mpr (contDiffOn_unstrAux_satSet hV hψsm)
  have hunsM : ContMDiffOn 𝓘(ℝ, Mod k) 𝓘(ℝ, Mod k) ∞ (fun v : Mod k => unstrAux ψ v) M₁ :=
    hunsSat.mono (by rw [hM₁]; exact inter_subset_right)
  have hsymmM : ContMDiffOn 𝓘(ℝ, Mod k) (𝓡∂ (8 + k + 1)) ∞
      (fun v : Mod k => (𝓡∂ (8 + k + 1)).symm (unstrAux ψ v)) M₁ :=
    (ModelWithCorners.contMDiffOn_symm (𝓡∂ (8 + k + 1))).comp hunsM (fun v hv => by
      have hvR : v ∈ Set.range (𝓡∂ (8 + k + 1)) := hv.1.1.1
      have hv0 : 0 ≤ v.ofLp 0 := by rwa [range_modelWithCornersEuclideanHalfSpace] at hvR
      rw [range_modelWithCornersEuclideanHalfSpace]
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [unstrAux_ofLp_zero]
      linarith [hv0, hψnn (tailVec v)])
  have hgM : ContMDiffOn 𝓘(ℝ, Mod k) (𝓡∂ (8 + k + 1)) ∞ g M₁ := by
    rw [hg]
    exact (contMDiffOn_symm_of_mem_maximalAtlas hφ).comp hsymmM (fun v hv => hv.1.1.2)
  have hcvW : ContMDiffOn (𝓡∂ (8 + k + 1)) 𝓘(ℝ, Mod k) ∞ (S.chartVec w₀) W := by
    rw [hW]
    exact (contMDiffOn_iff_contDiffOn.mpr (S.T_smooth w₀)).comp
      ((OpenPartialHomeomorph.contMDiffOn_extend (S.dom_maximalAtlas w₀)).mono
        (fun a ha => ha.1)) (fun a ha => ha.2)
  have hlocWithin : ContDiffWithinAt ℝ ∞ Loc' M₁ u₀.1 := by
    have houter : ContMDiffWithinAt (𝓡∂ (8 + k + 1)) 𝓘(ℝ, Mod k) ∞
        (S.chartVec w₀) W (g u₀.1) := hcvW (g u₀.1) hgW
    have hinner : ContMDiffWithinAt 𝓘(ℝ, Mod k) (𝓡∂ (8 + k + 1)) ∞ g M₁ u₀.1 :=
      hgM u₀.1 hu₀M₁
    have hcomp := houter.comp (u₀.1) hinner (fun v hv => hv.1.2)
    rw [hLoc']
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp hcomp
  -- ## the two expressions agree on `T`
  have hptwise : ∀ v : Mod k, v ∈ T →
      e.symm ((𝓡∂ (8 + k + 1)).symm v) ∈ S.chartSource w₀ → Loc v = Loc' v := by
    intro v hv hvc
    have hvT : (𝓡∂ (8 + k + 1)).symm v ∈ chartTgt S φ ψ V := hv.1
    have hvR : v ∈ Set.range (𝓡∂ (8 + k + 1)) := hv.2
    have hsymmv : ((𝓡∂ (8 + k + 1)).symm v).1 = v :=
      modelWithCorners_halfSpace_symm_coe hvR
    have hev : e.symm ((𝓡∂ (8 + k + 1)).symm v)
        = (⟨φ.symm (⟨unstrAux ψ ((𝓡∂ (8 + k + 1)).symm v).1,
              unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := (𝓡∂ (8 + k + 1)).symm v)⟩ : Half k),
            chartTgt_mem_region (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hψnn hvT⟩ : S.Region) := by
      rw [he]
      exact regionChart_symm_apply_of_mem (S := S) (φ := φ) (ψ := ψ) (V := V)
        (hV := hV) (hepi := hepi) (hψnn := hψnn) (hψsm := hψsm) (hxsrc := hxsrc) (hxV := hxV) hvT
    have hv0 : 0 ≤ v.ofLp 0 := by rwa [range_modelWithCornersEuclideanHalfSpace] at hvR
    have hmemv : 0 ≤ (unstrAux ψ v).ofLp 0 := by
      rw [unstrAux_ofLp_zero]
      exact add_nonneg hv0 (hψnn (tailVec v))
    have harg : (⟨unstrAux ψ ((𝓡∂ (8 + k + 1)).symm v).1,
          unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := (𝓡∂ (8 + k + 1)).symm v)⟩ : Half k)
        = (𝓡∂ (8 + k + 1)).symm (unstrAux ψ v) := by
      apply Subtype.ext
      show unstrAux ψ ((𝓡∂ (8 + k + 1)).symm v).1
        = ((𝓡∂ (8 + k + 1)).symm (unstrAux ψ v)).1
      rw [hsymmv]
      exact (modelWithCorners_halfSpace_symm_coe (v := unstrAux ψ v) (by
        rw [range_modelWithCornersEuclideanHalfSpace]; exact hmemv)).symm
    rw [hLoc, hLoc', hg]
    show (S.chartAt w₀).extend (𝓡∂ (8 + k + 1)) (e.symm ((𝓡∂ (8 + k + 1)).symm v))
      = S.chartVec w₀ (φ.symm ((𝓡∂ (8 + k + 1)).symm (unstrAux ψ v)))
    rw [S.chartAt_extend_apply_of_mem hvc]
    show S.T w₀ (S.domExt w₀ (e.symm ((𝓡∂ (8 + k + 1)).symm v)).1)
      = S.T w₀ (S.domExt w₀ (φ.symm ((𝓡∂ (8 + k + 1)).symm (unstrAux ψ v))))
    congr 1
    congr 1
    rw [hev]
    show φ.symm (⟨unstrAux ψ ((𝓡∂ (8 + k + 1)).symm v).1,
        unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := (𝓡∂ (8 + k + 1)).symm v)⟩ : Half k)
      = φ.symm ((𝓡∂ (8 + k + 1)).symm (unstrAux ψ v))
    rw [harg]
  -- ## the set `M₁` is a neighbourhood of `u₀.1` in `T`
  have hsymmcont : ContinuousAt (fun v : Mod k => (𝓡∂ (8 + k + 1)).symm (unstrAux ψ v)) u₀.1 :=
    ContinuousAt.comp (x := u₀.1) ((𝓡∂ (8 + k + 1)).continuous_symm.continuousAt)
      hunsAt.continuousAt
  have hgcont : ContinuousAt g u₀.1 := by
    rw [hg]
    exact ContinuousAt.comp (x := u₀.1)
      (φ.continuousOn_symm.continuousAt (φ.open_target.mem_nhds hmemφ)) hsymmcont
  have hpath : ((fun v : Mod k => (𝓡∂ (8 + k + 1)).symm (unstrAux ψ v)) ⁻¹' φ.target
      ∩ g ⁻¹' W) ∈ 𝓝 u₀.1 :=
    Filter.inter_mem
      (hsymmcont.preimage_mem_nhds (φ.open_target.mem_nhds hmemφ))
      (hgcont.preimage_mem_nhds (hWopen.mem_nhds hgW))
  have hU : ((fun v : Mod k => (𝓡∂ (8 + k + 1)).symm (unstrAux ψ v)) ⁻¹' φ.target ∩ g ⁻¹' W)
      ∩ satSet V ∈ 𝓝 u₀.1 :=
    Filter.inter_mem hpath ((isOpen_satSet hV).mem_nhds (subset_chartTgt_satSet hu₀))
  have hM₁nhds : M₁ ∈ 𝓝[T] u₀.1 := by
    refine mem_of_superset (Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hU)) ?_
    rintro v ⟨hvT, hvU⟩
    rw [hM₁, hN₁]
    exact ⟨⟨⟨hvT.2, hvU.1.1⟩, hvU.1.2⟩, hvU.2⟩
  have hcontw : ContinuousAt (fun v : Mod k => e.symm ((𝓡∂ (8 + k + 1)).symm v)) u₀.1 := by
    have h1 : ContinuousAt (fun v : Mod k => (𝓡∂ (8 + k + 1)).symm v) u₀.1 :=
      (𝓡∂ (8 + k + 1)).continuous_symm.continuousAt
    have h2 : ContinuousAt e.symm ((𝓡∂ (8 + k + 1)).symm u₀.1) :=
      e.continuousOn_invFun.continuousAt
        ((isOpen_chartTgt (S := S) (φ := φ) (ψ := ψ) (V := V) hV hψnn hψsm).mem_nhds (by
          rw [modelWithCorners_halfSpace_symm_eq (n := 8 + k + 1) u₀.2]
          exact hu₀))
    exact h2.comp h1
  have hv₀T : u₀.1 ∈ T := by
    refine ⟨?_, hu₀range⟩
    show (extChartAt (𝓡∂ (8 + k + 1)) u₀).symm u₀.1 ∈ chartTgt S φ ψ V
    rw [WeakRegion.RegionSetupWeak.extChartAt_self_symm_apply]
    rw [modelWithCorners_halfSpace_symm_eq (n := 8 + k + 1) u₀.2]
    exact hu₀
  have hw₀mem : e.symm ((𝓡∂ (8 + k + 1)).symm u₀.1) ∈ S.chartSource w₀ := by
    have hid : (𝓡∂ (8 + k + 1)).symm u₀.1 = u₀ := by
      rw [modelWithCorners_halfSpace_symm_eq (n := 8 + k + 1) u₀.2]
      rfl
    rw [hid, ← hw₀]
    exact S.mem_chartSource_self w₀
  have heq : Loc' =ᶠ[𝓝[T] u₀.1] Loc := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds
        (hcontw.preimage_mem_nhds ((S.isOpen_chartSource w₀).mem_nhds hw₀mem))]
      with v hv hvc
    exact (hptwise v hv hvc).symm
  -- ## conclusion
  have hbase : extChartAt (𝓡∂ (8 + k + 1)) u₀ u₀ = u₀.1 := by
    rw [extChartAt_self_apply]
    rfl
  have h1 : ContDiffWithinAt ℝ ∞ Loc' T u₀.1 :=
    hlocWithin.mono_of_mem_nhdsWithin hM₁nhds
  have h2 : ContDiffWithinAt ℝ ∞ Loc T u₀.1 :=
    h1.congr_of_eventuallyEq heq.symm (hptwise u₀.1 hv₀T hw₀mem)
  rw [hbase]
  exact h2

/-- **The straightening chart of the region at a point, in the maximal atlas.**

`S : RegionSetupWeak k` is the region `{Φ ≤ 0}` of a smooth function `Φ` on the half-space
`S.A = EuclideanHalfSpace (8+k+1)`; `φ` is an ambient chart of the maximal atlas of `S.A`, `ψ` a
nonnegative smooth function of the tangential coordinates and `V` an open set on which the region is
the epigraph `{ψ (tail z) ≤ z 0}` of `ψ` in the chart `φ`.  Then the graph straightening
`w ↦ strAux ψ (φ w 1)` is a chart of the maximal atlas of the region `S.Region`.

NOTE to the prover: prove this from scratch.  Do NOT import
`Submission/Work/PTGeometric/exists_regionStraightChart.lean` (it contains exactly this statement
with a `sorry`, and importing it would poison the proof). -/
theorem regionStraightChart_exists {k : ℕ}
    (S : Work.PTGeometric.WeakRegion.RegionSetupWeak k)
    (φ : OpenPartialHomeomorph S.A (Work.PTGeometric.Half k))
    (hφ : φ ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (8 + k + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) S.A)
    (ψ : Work.PTGeometric.Mod k → ℝ) (V : Set (Work.PTGeometric.Mod k))
    (hV : IsOpen V) (x : S.Region) (hxsrc : x.1 ∈ φ.source) (hxV : (φ x.1).1 ∈ V)
    (hepi : ∀ (z : Work.PTGeometric.Mod k) (hzV : z ∈ V) (hz : 0 ≤ z.ofLp 0),
      (S.Φ (φ.symm ⟨z, hz⟩) ≤ 0 ↔ ψ (Work.PTGeometric.tailVec z) ≤ z.ofLp 0))
    (hψnn : ∀ u : Work.PTGeometric.Mod k, 0 ≤ ψ u)
    (hψsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Work.PTGeometric.Mod k => ψ (Work.PTGeometric.tailVec z)) V) :
    ∃ e : OpenPartialHomeomorph S.Region (Work.PTGeometric.Half k),
      e ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (8 + k + 1))
        ((⊤ : ℕ∞) : WithTop ℕ∞) S.Region ∧
      x ∈ e.source ∧
      (∀ w ∈ e.source, (e w).1 = Work.PTGeometric.strAux ψ (φ w.1).1) ∧
      (∀ u ∈ e.target, (e.symm u).1 ∈ φ.source ∧
        (φ ((e.symm u).1)).1 = Work.PTGeometric.unstrAux ψ u.1) := by
  refine ⟨regionChart S φ ψ V hV hepi hψnn hψsm x hxsrc hxV, ?_, ?_, ?_, ?_⟩
  · exact (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).mpr
      ⟨contMDiffOn_regionChart_toFun hφ hV hepi hψnn hψsm x hxsrc hxV,
        contMDiffOn_regionChart_symm hφ hV hepi hψnn hψsm x hxsrc hxV⟩
  · exact ⟨hxsrc, hxV⟩
  · intro w hw
    rw [regionChart_apply_of_mem (S := S) (φ := φ) (ψ := ψ) (V := V) (hV := hV)
      (hepi := hepi) (hψnn := hψnn) (hψsm := hψsm) (hxsrc := hxsrc) (hxV := hxV) hw]
  · intro u hu
    have hcoe : ((regionChart S φ ψ V hV hepi hψnn hψsm x hxsrc hxV).symm u).1
        = φ.symm (⟨unstrAux ψ u.1,
            unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)⟩ : Half k) :=
      congrArg Subtype.val (regionChart_symm_apply_of_mem (S := S) (φ := φ) (ψ := ψ) (V := V)
        (hV := hV) (hepi := hepi) (hψnn := hψnn) (hψsm := hψsm) (hxsrc := hxsrc) (hxV := hxV) hu)
    have hT : (⟨unstrAux ψ u.1, unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)⟩ : Half k)
        ∈ φ.target :=
      half_ext_choose hu.2 (unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u))
    refine ⟨?_, ?_⟩
    · rw [hcoe]
      exact φ.map_target hT
    · rw [hcoe, phi_phi_symm (φ := φ) hT]

end

end Work.PTGeometric
