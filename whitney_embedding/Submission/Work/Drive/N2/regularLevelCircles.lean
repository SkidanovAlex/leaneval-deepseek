import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.OneDim.classify_connected_one_manifold
import Submission.Work.Drive.N2.LevelSetDefs
import Submission.Work.Drive.N2.levelModelExists
import Submission.Work.Drive.N2.circleDiffeomorphCompactConnected

/-!
# A regular level set of a smooth function on a compact surface is a finite union of circles

This file proves `Work.Drive.N2.regularLevelCircles`: a nonempty regular level set of a smooth
function on a compact surface is the union of the images of finitely many smoothly embedded
circles with pairwise disjoint images.

The proof equips the level set with the structure of a smooth `1`-manifold, using the local graph
model `Work.Drive.N2.levelModelExists` (`LevelSetDefs.lean`): in the chart at a point of the level
set, the level set is locally the graph of a smooth function of one coordinate.  The connected
components of the level set are then compact connected smooth `1`-manifolds, hence — by
`Work.OneDim.classify_connected_one_manifold` and compactness — diffeomorphic to `Circle`; and a
compact locally connected space has finitely many connected components.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Filter
open Work.Drive.Morse

noncomputable section

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace E2 M] [IsManifold (𝓡 2) ∞ M]

/-- The standard linear isometry `ℝ ≃L E1`. -/
def stdE1 : ℝ ≃L[ℝ] E1 :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

@[simp] theorem stdE1_apply (s : ℝ) : (stdE1 s).ofLp 0 = s := by
  simp [stdE1]

/-- The `i`-th coordinate of a point of the model surface, as a continuous linear map. -/
def levelCoordProj (i : Fin 2) : E2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i

@[simp] theorem levelCoordProj_apply (i : Fin 2) (v : E2) : levelCoordProj i v = v.ofLp i :=
  PiLp.proj_apply 2 (fun _ : Fin 2 => ℝ) i v

/-- **The regularity hypothesis** on a smooth function `f : M → ℝ` at a value `t`: `f` is smooth
and `t` is a regular value, i.e. no critical point of `f` lies over `t`.  It is a class so that the
manifold structure constructed below on the level set can be an instance. -/
class LevelHyp (f : M → ℝ) (t : ℝ) : Prop where
  /-- `f` is smooth -/
  contMDiff : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f
  /-- `t` is a regular value of `f` -/
  regular : ∀ x : M, f x = t → ¬ IsCritical f x

section Model

variable (f : M → ℝ) (t : ℝ) [LevelHyp f t]

/-- The local graph model of the level set at a point `y` of the level set. -/
noncomputable def mainModel (y : LevelSet f t) : LevelModel f t y :=
  let h := ‹LevelHyp f t›
  Classical.choice (levelModelExists f t h.contMDiff y (h.regular y.1 y.2))

/-- The chart coordinate of a point of the surface, seen in the chart at `y`. -/
noncomputable def coordOf (y : LevelSet f t) (x : M) : ℝ :=
  levelCoordProj (mainModel f t y).i ((chartAt E2 y.1) x)

/-- The parametrisation of the level set which inverts the chart at `y`. -/
noncomputable def levelParam (y : LevelSet f t) (s : ℝ) : M :=
  (chartAt E2 y.1).symm ((mainModel f t y).η s)

/-- The source of the chart of the level set at `y`. -/
def levelSource (y : LevelSet f t) : Set (LevelSet f t) :=
  {z | z.1 ∈ (chartAt E2 y.1).source ∧ (chartAt E2 y.1) z.1 ∈ (mainModel f t y).V}

/-- The target of the chart of the level set at `y`. -/
def levelTarget (y : LevelSet f t) : Set E1 :=
  stdE1 '' (mainModel f t y).T

/-- The source of the chart of the level set at `y` is open in the level set. -/
theorem levelSource_open (y : LevelSet f t) : IsOpen (levelSource f t y) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨hzsrc, hzV⟩ := hz
  have hc : ContinuousAt (chartAt E2 y.1) z.1 :=
    ((chartAt E2 y.1).continuousOn_toFun).continuousAt
      ((chartAt E2 y.1).open_source.mem_nhds hzsrc)
  have hcont : ContinuousAt (fun z : LevelSet f t => (chartAt E2 y.1) z.1) z :=
    hc.comp continuous_subtype_val.continuousAt
  have h1 : {z : LevelSet f t | z.1 ∈ (chartAt E2 y.1).source} ∈ 𝓝 z :=
    ((chartAt E2 y.1).open_source.preimage continuous_subtype_val).mem_nhds hzsrc
  have h2 : {z : LevelSet f t |
      (chartAt E2 y.1) z.1 ∈ (mainModel f t y).V} ∈ 𝓝 z :=
    hcont.preimage_mem_nhds ((mainModel f t y).isOpen_V.mem_nhds hzV)
  exact Filter.mem_of_superset (Filter.inter_mem h1 h2) (fun w hw => hw)

/-- The target of the chart of the level set at `y` is open. -/
theorem levelTarget_open (y : LevelSet f t) : IsOpen (levelTarget f t y) := by
  have h : levelTarget f t y = stdE1.symm ⁻¹' (mainModel f t y).T := by
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
    · intro hw
      exact ⟨stdE1.symm w, hw, stdE1.apply_symm_apply w⟩
  rw [h]
  exact (mainModel f t y).isOpen_T.preimage stdE1.symm.continuous

/-- The coordinate of a point of the source lies in `T`. -/
theorem coordOf_mem_T (y : LevelSet f t) {z : M}
    (hz : z ∈ (chartAt E2 y.1).source)
    (hzV : (chartAt E2 y.1) z ∈ (mainModel f t y).V) (hzt : f z = t) :
    coordOf f t y z ∈ (mainModel f t y).T := by
  have hfz : f ((chartAt E2 y.1).symm ((chartAt E2 y.1) z)) = t := by
    rw [OpenPartialHomeomorph.left_inv _ hz]
    exact hzt
  have := (mainModel f t y).mem_T ((chartAt E2 y.1) z) hzV hfz
  simpa only [coordOf, levelCoordProj_apply] using this

/-- The parametrisation inverts the coordinate on the source. -/
theorem levelParam_coordOf (y : LevelSet f t) {z : M}
    (hz : z ∈ (chartAt E2 y.1).source)
    (hzV : (chartAt E2 y.1) z ∈ (mainModel f t y).V) (hzt : f z = t) :
    levelParam f t y (coordOf f t y z) = z := by
  have hfz : f ((chartAt E2 y.1).symm ((chartAt E2 y.1) z)) = t := by
    rw [OpenPartialHomeomorph.left_inv _ hz]
    exact hzt
  have hg := (mainModel f t y).graph ((chartAt E2 y.1) z) hzV hfz
  rw [levelParam, coordOf, levelCoordProj_apply]
  rw [hg, OpenPartialHomeomorph.left_inv _ hz]

/-- The parametrisation lands in the source of the chart. -/
theorem levelParam_mem_source (y : LevelSet f t) {s : ℝ}
    (hs : s ∈ (mainModel f t y).T) :
    levelParam f t y s ∈ (chartAt E2 y.1).source ∧
      (chartAt E2 y.1) (levelParam f t y s) ∈ (mainModel f t y).V := by
  have htarget := (mainModel f t y).mem_target s hs
  constructor
  · rw [levelParam]
    exact OpenPartialHomeomorph.map_target _ htarget
  · rw [levelParam, OpenPartialHomeomorph.right_inv _ htarget]
    exact (mainModel f t y).mem_V s hs

/-- The coordinate of the parametrised point is `s`. -/
theorem coordOf_levelParam (y : LevelSet f t) {s : ℝ}
    (hs : s ∈ (mainModel f t y).T) :
    coordOf f t y (levelParam f t y s) = s := by
  have htarget := (mainModel f t y).mem_target s hs
  rw [coordOf, levelCoordProj_apply, levelParam, OpenPartialHomeomorph.right_inv _ htarget]
  exact (mainModel f t y).coord s hs

/-- The parametrisation is smooth as a map into the surface. -/
theorem levelParam_contMDiffOn (y : LevelSet f t) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ (levelParam f t y) (mainModel f t y).T := by
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) ∞ (mainModel f t y).η (mainModel f t y).T :=
    contMDiffOn_iff_contDiffOn.mpr (mainModel f t y).contDiffOn_η
  have hc : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ (chartAt E2 y.1).symm
      (chartAt E2 y.1).target := contMDiffOn_chart_symm
  have hcomp := hc.comp hη (fun s hs => (mainModel f t y).mem_target s hs)
  show ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞
    (fun s => (chartAt E2 y.1).symm ((mainModel f t y).η s)) (mainModel f t y).T
  exact hcomp

/-- The inverse of the chart at `y`, as a (total) function into the level set. -/
noncomputable def levelInv (y : LevelSet f t) (w : E1) : LevelSet f t := by
  classical
  exact if h : stdE1.symm w ∈ (mainModel f t y).T then
    ⟨levelParam f t y (stdE1.symm w), (mainModel f t y).level _ h⟩
  else y

/-- The chart of the level set at `y`, with model space `E1`. -/
noncomputable def levelChart (y : LevelSet f t) : OpenPartialHomeomorph (LevelSet f t) E1 :=
  OpenPartialHomeomorph.mk
    { toFun := fun z => stdE1 (coordOf f t y z.1)
      invFun := levelInv f t y
      source := levelSource f t y
      target := levelTarget f t y
      map_source' := fun z hz => by
        refine ⟨coordOf f t y z.1, ?_, rfl⟩
        exact coordOf_mem_T f t y hz.1 hz.2 z.2
      map_target' := fun w hw => by
        obtain ⟨s, hs, rfl⟩ := hw
        have hs' : stdE1.symm (stdE1 s) ∈ (mainModel f t y).T := by simpa using hs
        rw [levelInv, dif_pos hs']
        exact levelParam_mem_source f t y hs'
      left_inv' := fun z hz => by
        have hT : stdE1.symm (stdE1 (coordOf f t y z.1)) ∈ (mainModel f t y).T := by
          simpa using coordOf_mem_T f t y hz.1 hz.2 z.2
        rw [levelInv, dif_pos hT]
        refine Subtype.ext ?_
        show levelParam f t y (stdE1.symm (stdE1 (coordOf f t y z.1))) = z.1
        rw [stdE1.symm_apply_apply]
        exact levelParam_coordOf f t y hz.1 hz.2 z.2
      right_inv' := fun w hw => by
        obtain ⟨s, hs, rfl⟩ := hw
        have hs' : stdE1.symm (stdE1 s) ∈ (mainModel f t y).T := by simpa using hs
        rw [levelInv, dif_pos hs']
        show stdE1 (coordOf f t y (levelParam f t y (stdE1.symm (stdE1 s)))) = stdE1 s
        rw [coordOf_levelParam f t y hs']
        simp
      continuousOn_toFun := by
        intro z hz
        have hc : ContinuousAt (chartAt E2 y.1) z.1 :=
          ((chartAt E2 y.1).continuousOn_toFun).continuousAt
            ((chartAt E2 y.1).open_source.mem_nhds hz.1)
        have h1 : ContinuousAt (coordOf f t y) z.1 :=
          (ContinuousAt.comp (g := levelCoordProj (mainModel f t y).i)
            (levelCoordProj (mainModel f t y).i).continuous.continuousAt hc)
        have h2 : ContinuousAt (fun z : LevelSet f t => coordOf f t y z.1) z :=
          h1.comp continuous_subtype_val.continuousAt
        exact (stdE1.continuous.continuousAt.comp h2).continuousWithinAt
      continuousOn_invFun := by
        have hbase : ContinuousOn (fun w : E1 => levelParam f t y (stdE1.symm w))
            (levelTarget f t y) := by
          have h1 : ContinuousOn (levelParam f t y) (mainModel f t y).T :=
            (levelParam_contMDiffOn f t y).continuousOn
          refine h1.comp stdE1.symm.continuous.continuousOn ?_
          intro w hw
          obtain ⟨s, hs, rfl⟩ := hw
          simpa using hs
        have hval : ContinuousOn (fun w : E1 => (levelInv f t y w).1)
            (levelTarget f t y) :=
          hbase.congr (fun w hw => by
            obtain ⟨s, hs, rfl⟩ := hw
            have hs' : stdE1.symm (stdE1 s) ∈ (mainModel f t y).T := by simpa using hs
            rw [levelInv, dif_pos hs'])
        exact Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hval }
    (levelSource_open f t y) (levelTarget_open f t y)

theorem levelChart_source (y : LevelSet f t) :
    (levelChart f t y).source = levelSource f t y := rfl

theorem levelChart_target (y : LevelSet f t) :
    (levelChart f t y).target = levelTarget f t y := rfl

theorem levelChart_apply (y : LevelSet f t) (z : LevelSet f t) :
    levelChart f t y z = stdE1 (coordOf f t y z.1) := rfl

theorem levelChart_symm_apply (y : LevelSet f t) (w : E1) :
    (levelChart f t y).symm w = levelInv f t y w := rfl

/-- The underlying point of the inverse of the chart, for `w` in the target. -/
theorem levelInv_coe_of_mem (y : LevelSet f t) {w : E1} (hw : w ∈ levelTarget f t y) :
    (levelInv f t y w).1 = levelParam f t y (stdE1.symm w) := by
  have h' : stdE1.symm w ∈ (mainModel f t y).T := by
    obtain ⟨s, hs, rfl⟩ := hw
    simpa using hs
  rw [levelInv, dif_pos h']

/-- **The charted space structure on the level set** afforded by the charts `levelChart`. -/
noncomputable instance levelChartedSpace : ChartedSpace E1 (LevelSet f t) where
  atlas := Set.range (levelChart f t)
  chartAt := levelChart f t
  mem_chart_source := fun y => by
    refine ⟨mem_chart_source E2 y.1, ?_⟩
    have h := (mainModel f t y).mem_V _ (mainModel f t y).base_mem_T
    rwa [(mainModel f t y).base_eq] at h
  chart_mem_atlas := fun y => ⟨y, rfl⟩

/-- **The transition function between two charts is smooth.**  On the source of the composition, the
transition function is `w ↦ stdE1 (coord (chartAt ℝ² y') (levelParam y (stdE1.symm w)))`, which is
smooth as a composite of the smooth parametrisation at `y`, the smooth chart at `y'` and linear
maps. -/
theorem levelChart_transition_contDiffOn (y y' : LevelSet f t) :
    ContDiffOn ℝ ∞ (fun w : E1 => levelChart f t y' ((levelChart f t y).symm w))
      ((levelChart f t y).symm.trans (levelChart f t y')).source := by
  set S := ((levelChart f t y).symm.trans (levelChart f t y')).source with hS
  have hT : ∀ w ∈ S, w ∈ (levelChart f t y).target := by
    intro w hw
    rw [hS, OpenPartialHomeomorph.trans_source] at hw
    exact hw.1
  have hsub : ∀ w ∈ S, stdE1.symm w ∈ (mainModel f t y).T := by
    intro w hw
    have hw' := hT w hw
    rw [levelChart_target, levelTarget] at hw'
    obtain ⟨s, hs, hsr⟩ := hw'
    rw [← hsr]
    simpa using hs
  have hstd : ContMDiffOn 𝓘(ℝ, E1) 𝓘(ℝ, ℝ) ∞ (⇑stdE1.symm) S :=
    contMDiffOn_iff_contDiffOn.mpr
      (stdE1.symm.contDiff.contDiffOn.mono (Set.subset_univ S))
  have h1 : ContMDiffOn 𝓘(ℝ, E1) (𝓡 2) ∞ (fun w => levelParam f t y (stdE1.symm w)) S :=
    (levelParam_contMDiffOn f t y).comp hstd (fun w hw => hsub w hw)
  have hmem : ∀ w ∈ S, levelParam f t y (stdE1.symm w) ∈ (chartAt E2 y'.1).source := by
    intro w hw
    have hw' : (levelChart f t y).symm w ∈ levelSource f t y' := by
      rw [hS, OpenPartialHomeomorph.trans_source] at hw
      rw [← levelChart_source]
      exact hw.2
    have h3 : ((levelChart f t y).symm w).1 = levelParam f t y (stdE1.symm w) := by
      rw [levelChart_symm_apply]
      exact levelInv_coe_of_mem f t y (hT w hw)
    have h4 := hw'.1
    rwa [h3] at h4
  have h2 : ContMDiffOn 𝓘(ℝ, E1) 𝓘(ℝ, E2) ∞
      (fun w => (chartAt E2 y'.1) (levelParam f t y (stdE1.symm w))) S :=
    (contMDiffOn_chart (I := 𝓡 2) (x := y'.1)).comp h1 hmem
  have h3 : ContDiffOn ℝ ∞ (fun w => (chartAt E2 y'.1) (levelParam f t y (stdE1.symm w))) S :=
    contMDiffOn_iff_contDiffOn.mp h2
  have h4 : ContDiffOn ℝ ∞ (fun w => stdE1 (levelCoordProj (mainModel f t y').i
      ((chartAt E2 y'.1) (levelParam f t y (stdE1.symm w))))) S :=
    stdE1.contDiff.comp_contDiffOn
      ((levelCoordProj (mainModel f t y').i).contDiff.comp_contDiffOn h3)
  exact h4.congr (fun w hw => by
    show levelChart f t y' ((levelChart f t y).symm w) = _
    rw [← levelInv_coe_of_mem f t y (hT w hw)]
    rfl)

/-- The transition function belongs to the `C^∞` groupoid: this is the compatibility of the charts
`levelChart`. -/
theorem levelChart_transition_mem (y y' : LevelSet f t) :
    (levelChart f t y).symm.trans (levelChart f t y') ∈ contDiffGroupoid ∞ I1 := by
  constructor
  · intro x hx
    show ContDiffWithinAt ℝ ∞ (fun w : E1 => levelChart f t y' ((levelChart f t y).symm w))
      (I1.symm ⁻¹' ((levelChart f t y).symm.trans (levelChart f t y')).source ∩ Set.range I1) x
    refine ((levelChart_transition_contDiffOn f t y y').contDiffWithinAt ?_).mono
      (fun z hz => by simpa [modelWithCornersSelf_coe_symm] using hz.1)
    simpa [modelWithCornersSelf_coe_symm] using hx.1
  · intro x hx
    have hsymm : ((levelChart f t y).symm.trans (levelChart f t y')).symm =
        (levelChart f t y').symm.trans (levelChart f t y) :=
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm ..
    rw [hsymm]
    show ContDiffWithinAt ℝ ∞ (fun w : E1 => levelChart f t y ((levelChart f t y').symm w))
      (I1.symm ⁻¹' ((levelChart f t y').symm.trans (levelChart f t y)).source ∩
        Set.range I1) x
    refine ((levelChart_transition_contDiffOn f t y' y).contDiffWithinAt ?_).mono
      (fun z hz => by simpa [modelWithCornersSelf_coe_symm] using hz.1)
    simpa [modelWithCornersSelf_coe_symm] using hx.1

/-- **The level set of a regular level of a smooth function on a surface is a smooth `1`-manifold**,
with the charts `levelChart`. -/
noncomputable instance levelIsManifold : IsManifold I1 ∞ (LevelSet f t) where
  compatible := by
    intro e e' he he'
    obtain ⟨y, rfl⟩ := he
    obtain ⟨y', rfl⟩ := he'
    exact levelChart_transition_mem f t y y'

/-- The ambient chart at `y`, composed with the parametrisation at `y`, is smooth on the target of
the chart of the level set. -/
theorem chartAt_levelParam_contMDiffOn (y : LevelSet f t) :
    ContMDiffOn 𝓘(ℝ, E1) 𝓘(ℝ, E2) ∞
      (fun w => (chartAt E2 y.1) (levelParam f t y (stdE1.symm w)))
      (levelChart f t y).target := by
  have hsub : ∀ w ∈ (levelChart f t y).target, stdE1.symm w ∈ (mainModel f t y).T := by
    intro w hw
    rw [levelChart_target, levelTarget] at hw
    obtain ⟨s, hs, hsr⟩ := hw
    rw [← hsr]
    simpa using hs
  have hstd : ContMDiffOn 𝓘(ℝ, E1) 𝓘(ℝ, ℝ) ∞ (⇑stdE1.symm) (levelChart f t y).target :=
    contMDiffOn_iff_contDiffOn.mpr
      (stdE1.symm.contDiff.contDiffOn.mono (Set.subset_univ _))
  have h1 : ContMDiffOn 𝓘(ℝ, E1) (𝓡 2) ∞ (fun w => levelParam f t y (stdE1.symm w))
      (levelChart f t y).target :=
    (levelParam_contMDiffOn f t y).comp hstd hsub
  exact (contMDiffOn_chart (I := 𝓡 2) (x := y.1)).comp h1
    (fun w hw => (levelParam_mem_source f t y (hsub w hw)).1)

/-- The parametrisation at `y`, read through the inverse of the model coordinate, is smooth on the
target of the chart of the level set. -/
theorem levelParam_comp_contMDiffOn (y : LevelSet f t) :
    ContMDiffOn 𝓘(ℝ, E1) (𝓡 2) ∞ (fun w => levelParam f t y (stdE1.symm w))
      (levelChart f t y).target := by
  have hsub : ∀ w ∈ (levelChart f t y).target, stdE1.symm w ∈ (mainModel f t y).T := by
    intro w hw
    rw [levelChart_target, levelTarget] at hw
    obtain ⟨s, hs, hsr⟩ := hw
    rw [← hsr]
    simpa using hs
  have hstd : ContMDiffOn 𝓘(ℝ, E1) 𝓘(ℝ, ℝ) ∞ (⇑stdE1.symm) (levelChart f t y).target :=
    contMDiffOn_iff_contDiffOn.mpr
      (stdE1.symm.contDiff.contDiffOn.mono (Set.subset_univ _))
  exact (levelParam_contMDiffOn f t y).comp hstd hsub

/-- **The inclusion of the level set into the surface is smooth**, on the source of each chart. -/
theorem subtypeVal_contMDiffOn (y : LevelSet f t) :
    ContMDiffOn I1 (𝓡 2) ∞ (Subtype.val : LevelSet f t → M) (levelSource f t y) := by
  have hchart : ContMDiffOn I1 𝓘(ℝ, E1) ∞ (levelChart f t y) (levelSource f t y) :=
    contMDiffOn_chart (I := I1) (x := y)
  have hcomp := (levelParam_comp_contMDiffOn f t y).comp hchart
    (fun z hz => by
      show (levelChart f t y) z ∈ (levelChart f t y).target
      exact OpenPartialHomeomorph.map_source (levelChart f t y) hz)
  refine hcomp.congr (fun z hz => ?_)
  show (z : M) = (fun w => levelParam f t y (stdE1.symm w)) (levelChart f t y z)
  simp only [levelChart_apply, stdE1.symm_apply_apply]
  exact (levelParam_coordOf f t y hz.1 hz.2 z.2).symm

/-- **The inclusion of the level set into the surface is smooth.** -/
theorem subtypeVal_contMDiff :
    ContMDiff I1 (𝓡 2) ∞ (Subtype.val : LevelSet f t → M) := by
  refine contMDiff_of_contMDiffOn_iUnion_of_isOpen
    (s := fun y : LevelSet f t => levelSource f t y) (fun y => subtypeVal_contMDiffOn f t y)
    (fun y => levelSource_open f t y) ?_
  ext z
  exact ⟨fun _ => Set.mem_univ z,
    fun _ => Set.mem_iUnion.mpr ⟨z, mem_chart_source E1 z⟩⟩

end Model

section Final

variable (f : M → ℝ) (t : ℝ) [LevelHyp f t]
variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The level set of a smooth function is closed. -/
theorem levelSet_isClosed : IsClosed {x : M | f x = t} :=
  isClosed_eq (‹LevelHyp f t›).contMDiff.continuous continuous_const

/-- The level set of a smooth function on a compact surface is compact. -/
theorem levelSet_compactSpace : CompactSpace (LevelSet f t) :=
  isCompact_iff_compactSpace.mp (levelSet_isClosed f t).isCompact

/-- The level set of a smooth function on a surface is locally connected. -/
theorem levelSet_locallyConnectedSpace : LocallyConnectedSpace (LevelSet f t) :=
  ChartedSpace.locallyConnectedSpace E1 (LevelSet f t)

/-- A representative point of the connected component `i` of the level set. -/
noncomputable def compRep (i : ConnectedComponents (LevelSet f t)) : LevelSet f t :=
  Quotient.out (s := connectedComponentSetoid (LevelSet f t)) i

/-- The `i`-th connected component of the level set, as an open subset of the level set. -/
noncomputable def compOf (i : ConnectedComponents (LevelSet f t)) :
    TopologicalSpace.Opens (LevelSet f t) :=
  ⟨connectedComponent (compRep f t i), by
    haveI : LocallyConnectedSpace (LevelSet f t) := levelSet_locallyConnectedSpace f t
    exact isOpen_connectedComponent⟩

/-- The `i`-th connected component of the level set, as a subset of the surface. -/
def compSet (i : ConnectedComponents (LevelSet f t)) : Set M :=
  Subtype.val '' (compOf f t i : Set (LevelSet f t))

theorem compRep_mem (i : ConnectedComponents (LevelSet f t)) :
    compRep f t i ∈ (compOf f t i : Set (LevelSet f t)) :=
  mem_connectedComponent

theorem coe_compRep (i : ConnectedComponents (LevelSet f t)) :
    (compRep f t i : ConnectedComponents (LevelSet f t)) = i :=
  Quotient.out_eq i

theorem compSet_nonempty (i : ConnectedComponents (LevelSet f t)) :
    (compSet f t i).Nonempty :=
  ⟨(compRep f t i : M), compRep f t i, compRep_mem f t i, rfl⟩

theorem mem_compSet {i : ConnectedComponents (LevelSet f t)} {x : M} (hx : f x = t) :
    x ∈ compSet f t i ↔
      (⟨x, hx⟩ : LevelSet f t) ∈ connectedComponent (compRep f t i) := by
  constructor
  · rintro ⟨w, hw, hwr⟩
    have h : w = (⟨x, hx⟩ : LevelSet f t) := Subtype.ext hwr
    rwa [h] at hw
  · intro hw
    exact ⟨⟨x, hx⟩, hw, rfl⟩

/-- Distinct components of the level set are disjoint. -/
theorem disjoint_compSet (i j : ConnectedComponents (LevelSet f t)) (hij : i ≠ j) :
    Disjoint (compSet f t i) (compSet f t j) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨w, hw, hwr⟩ := hx
  obtain ⟨w', hw', hwr'⟩ := hx'
  have hww' : w = w' := Subtype.ext (hwr.trans hwr'.symm)
  have h1 : (w : ConnectedComponents (LevelSet f t)) =
      (compRep f t i : ConnectedComponents (LevelSet f t)) :=
    ConnectedComponents.coe_eq_coe'.mpr hw
  have h2 : (w : ConnectedComponents (LevelSet f t)) =
      (compRep f t j : ConnectedComponents (LevelSet f t)) :=
    ConnectedComponents.coe_eq_coe'.mpr (by rw [hww']; exact hw')
  refine hij ?_
  calc i = (compRep f t i : ConnectedComponents (LevelSet f t)) := (coe_compRep f t i).symm
    _ = (w : ConnectedComponents (LevelSet f t)) := h1.symm
    _ = (compRep f t j : ConnectedComponents (LevelSet f t)) := h2
    _ = j := coe_compRep f t j

/-- An injective continuous map from a compact space to a Hausdorff space is an embedding. -/
theorem isEmbedding_of_continuous_injective_of_compactSpace {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y] {g : X → Y}
    (hg : Continuous g) (hinj : Function.Injective g) : Topology.IsEmbedding g :=
  (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hg hinj
    (fun _ hs => (hs.isCompact.image hg).isClosed)).isEmbedding

/-- **Each connected component of the level set is a circle.** -/
theorem exists_circleMap_component (i : ConnectedComponents (LevelSet f t)) :
    ∃ Φ : Circle → M,
      ContMDiff (𝓡 1) (𝓡 2) ∞ Φ ∧ Function.Injective Φ ∧ Set.range Φ = compSet f t i := by
  haveI hLC : LocallyConnectedSpace (LevelSet f t) := levelSet_locallyConnectedSpace f t
  haveI hC : CompactSpace (LevelSet f t) := levelSet_compactSpace f t
  haveI hC' : CompactSpace (compOf f t i) :=
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  haveI hSCm : SecondCountableTopology (LevelSet f t) :=
    TopologicalSpace.secondCountableTopology_induced (LevelSet f t) M
      (Subtype.val : LevelSet f t → M)
  haveI hT2' : T2Space (compOf f t i) := inferInstance
  haveI hSC' : SecondCountableTopology (compOf f t i) :=
    TopologicalSpace.secondCountableTopology_induced (compOf f t i) (LevelSet f t)
      (Subtype.val : (compOf f t i) → LevelSet f t)
  haveI hConn : ConnectedSpace (compOf f t i) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  obtain ⟨ψ⟩ := circleDiffeomorphCompactConnected (C := compOf f t i)
  refine ⟨fun z => (((ψ z : compOf f t i) : LevelSet f t) : M), ?_, ?_, ?_⟩
  · exact (subtypeVal_contMDiff f t).comp
      ((contMDiff_subtype_val (n := ∞) (U := compOf f t i)).comp ψ.contMDiff)
  · intro z z' h
    have h1 : ((ψ z : compOf f t i) : LevelSet f t) = ((ψ z' : compOf f t i) : LevelSet f t) :=
      Subtype.ext (by simpa using h)
    exact ψ.toHomeomorph.injective (Subtype.ext h1)
  · ext y
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(ψ z : compOf f t i), (ψ z : compOf f t i).2, hz⟩
    · rintro ⟨w, hw, hw'⟩
      obtain ⟨z, hz⟩ := ψ.toHomeomorph.surjective ⟨w, hw⟩
      refine ⟨z, ?_⟩
      have hz' : (ψ z : compOf f t i) = ⟨w, hw⟩ := hz
      show (((ψ z : compOf f t i) : LevelSet f t) : M) = y
      rw [hz']
      exact hw'

end Final

open scoped Manifold ContDiff in
open Work.Drive.Morse in
/-- **A nonempty regular level set of a smooth function on a compact surface is a finite disjoint
union of circles.**  If `t` is a regular value (no critical point lies over it) and `t` is attained,
then `f ⁻¹' {t}` is the union of the images of finitely many smoothly embedded circles with pairwise
disjoint images.

Both the movie construction and the classification route need this in order to draw level sets in
`ℝ³`.  The encoding avoids `Fin N → Circle`, which is the *product* `(S¹)^N` (hence connected) rather
than a disjoint union. -/
theorem regularLevelCircles {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (t : ℝ) (ht : ∃ x : M, f x = t)
    (hreg : ∀ x : M, f x = t → ¬ IsCritical f x) :
    ∃ (ι : Type) (_ : Fintype ι) (Φ : ι → Circle → M),
      (∀ i : ι, ContMDiff (𝓡 1) (𝓡 2) ∞ (Φ i)) ∧
      (∀ i : ι, Topology.IsEmbedding (Φ i)) ∧
      (∀ i j : ι, i ≠ j → Disjoint (Set.range (Φ i)) (Set.range (Φ j))) ∧
      (⋃ i : ι, Set.range (Φ i)) = {x : M | f x = t} := by
  classical
  haveI : LevelHyp f t := ⟨hf, hreg⟩
  haveI hLC : LocallyConnectedSpace (LevelSet f t) := levelSet_locallyConnectedSpace f t
  haveI hC : CompactSpace (LevelSet f t) := levelSet_compactSpace f t
  haveI hne : Nonempty (LevelSet f t) := let ⟨x, hx⟩ := ht; ⟨⟨x, hx⟩⟩
  haveI : Fintype (ConnectedComponents (LevelSet f t)) := Fintype.ofFinite _
  let e := Fintype.equivFin (ConnectedComponents (LevelSet f t))
  refine ⟨Fin (Fintype.card (ConnectedComponents (LevelSet f t))), inferInstance,
    fun i => Classical.choose (exists_circleMap_component f t (e.symm i)), ?_, ?_, ?_, ?_⟩
  · intro i
    exact (Classical.choose_spec (exists_circleMap_component f t (e.symm i))).1
  · intro i
    exact isEmbedding_of_continuous_injective_of_compactSpace
      (Classical.choose_spec (exists_circleMap_component f t (e.symm i))).1.continuous
      (Classical.choose_spec (exists_circleMap_component f t (e.symm i))).2.1
  · intro i j hij
    have hij' : e.symm i ≠ e.symm j := fun h => hij (by
      rw [← e.apply_symm_apply i, ← e.apply_symm_apply j, h])
    rw [(Classical.choose_spec (exists_circleMap_component f t (e.symm i))).2.2,
      (Classical.choose_spec (exists_circleMap_component f t (e.symm j))).2.2]
    exact disjoint_compSet f t _ _ hij'
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rw [(Classical.choose_spec (exists_circleMap_component f t (e.symm i))).2.2] at hxi
      obtain ⟨w, -, hwr⟩ := hxi
      rw [← hwr]
      exact w.2
    · intro hx
      refine Set.mem_iUnion.mpr
        ⟨e (ConnectedComponents.mk (⟨x, hx⟩ : LevelSet f t)), ?_⟩
      rw [(Classical.choose_spec (exists_circleMap_component f t
        (e.symm (e (ConnectedComponents.mk (⟨x, hx⟩ : LevelSet f t)))))).2.2]
      rw [e.symm_apply_apply (ConnectedComponents.mk (⟨x, hx⟩ : LevelSet f t))]
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      show (⟨x, hx⟩ : LevelSet f t) ∈
        connectedComponent (compRep f t (ConnectedComponents.mk (⟨x, hx⟩ : LevelSet f t)))
      have hcc : connectedComponent (compRep f t (ConnectedComponents.mk (⟨x, hx⟩ : LevelSet f t)))
          = connectedComponent (⟨x, hx⟩ : LevelSet f t) :=
        ConnectedComponents.coe_eq_coe.mp (coe_compRep f t _)
      rw [hcc]
      exact mem_connectedComponent

end

end Work.Drive.N2
