import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

open Set Filter
open scoped Manifold Topology

namespace Commons.Geometry.Manifold

/-! ### Auxiliary facts about the identity model with corners on `ℂ` -/

private lemma mcs_self_coe : (↑(modelWithCornersSelf ℂ ℂ) : ℂ → ℂ) = id := rfl

private lemma mcs_self_coe_symm : (↑(modelWithCornersSelf ℂ ℂ).symm : ℂ → ℂ) = id := rfl

private lemma extChartAt_self_coe {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    ⇑(extChartAt (modelWithCornersSelf ℂ ℂ) x) = ⇑(chartAt ℂ x) := by
  rw [extChartAt_coe]
  funext z
  simp [Function.comp_apply]

private lemma extChartAt_self_coe_symm {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) :
    ⇑(extChartAt (modelWithCornersSelf ℂ ℂ) x).symm = ⇑(chartAt ℂ x).symm := by
  rw [extChartAt_coe_symm]
  funext z
  simp [Function.comp_apply]

private lemma extChartAt_self_target {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) :
    (extChartAt (modelWithCornersSelf ℂ ℂ) x).target = (chartAt ℂ x).target := by
  rw [extChartAt_target, mcs_self_coe_symm, mcs_self_coe]
  simp

/-! ### Analyticity of the transition between two charts -/

/-- The transition map between the chart at `a` and the chart at `b`, read as a map `ℂ → ℂ`,
is analytic at `(chartAt ℂ b) u` whenever `u` lies in the source of both charts. -/
private lemma analyticAt_chart_transition {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {a b u : X}
    (hu : u ∈ (chartAt ℂ b).source) (hu' : u ∈ (chartAt ℂ a).source) :
    AnalyticAt ℂ ((chartAt ℂ a) ∘ (chartAt ℂ b).symm) ((chartAt ℂ b) u) := by
  have hmem : ((chartAt ℂ b) u) ∈ ((extChartAt (modelWithCornersSelf ℂ ℂ) b).symm ≫
      extChartAt (modelWithCornersSelf ℂ ℂ) a).source := by
    rw [PartialEquiv.trans_source]
    refine ⟨?_, ?_⟩
    · rw [PartialEquiv.symm_source, extChartAt_self_target]
      exact (chartAt ℂ b).map_source hu
    · simp only [Set.mem_preimage]
      have hsymm : ⇑(extChartAt (modelWithCornersSelf ℂ ℂ) b).symm ((chartAt ℂ b) u) = u := by
        rw [extChartAt_self_coe_symm]
        exact (chartAt ℂ b).left_inv hu
      rw [hsymm, extChartAt_source]
      exact hu'
  have hopen : IsOpen ((extChartAt (modelWithCornersSelf ℂ ℂ) b).symm ≫
      extChartAt (modelWithCornersSelf ℂ ℂ) a).source := by
    rw [ext_coord_change_source, mcs_self_coe, Set.image_id]
    exact ((chartAt ℂ b).symm ≫ₕ (chartAt ℂ a)).open_source
  have hcdS : ContDiffOn ℂ 1 (⇑(extChartAt (modelWithCornersSelf ℂ ℂ) a) ∘
      ⇑(extChartAt (modelWithCornersSelf ℂ ℂ) b).symm) ((extChartAt (modelWithCornersSelf ℂ ℂ) b).symm ≫
      extChartAt (modelWithCornersSelf ℂ ℂ) a).source :=
    contDiffOn_ext_coord_change a b
  have hcd' : ContDiffOn ℂ 1 ((chartAt ℂ a) ∘ (chartAt ℂ b).symm) ((extChartAt (modelWithCornersSelf ℂ ℂ) b).symm ≫
      extChartAt (modelWithCornersSelf ℂ ℂ) a).source := by
    simpa only [extChartAt_self_coe, extChartAt_self_coe_symm] using hcdS
  exact (hcd'.differentiableOn_one).analyticAt (hopen.mem_nhds hmem)

/-- The chart-`b` representation of `f` agrees, near the image of `u`, with the composition of
the chart-`a` representation of `f` with the transition map from chart `b` to chart `a`. -/
private lemma chart_eventuallyEq {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {a b u : X}
    (hu : u ∈ (chartAt ℂ b).source) (hu' : u ∈ (chartAt ℂ a).source) (f : X → ℂ) :
    (f ∘ (chartAt ℂ b).symm) =ᶠ[𝓝 ((chartAt ℂ b) u)]
      ((f ∘ (chartAt ℂ a).symm) ∘ ((chartAt ℂ a) ∘ (chartAt ℂ b).symm)) := by
  have hmem : ((chartAt ℂ b) u) ∈ ((extChartAt (modelWithCornersSelf ℂ ℂ) b).symm ≫
      extChartAt (modelWithCornersSelf ℂ ℂ) a).source := by
    rw [PartialEquiv.trans_source]
    refine ⟨?_, ?_⟩
    · rw [PartialEquiv.symm_source, extChartAt_self_target]
      exact (chartAt ℂ b).map_source hu
    · simp only [Set.mem_preimage]
      have hsymm : ⇑(extChartAt (modelWithCornersSelf ℂ ℂ) b).symm ((chartAt ℂ b) u) = u := by
        rw [extChartAt_self_coe_symm]
        exact (chartAt ℂ b).left_inv hu
      rw [hsymm, extChartAt_source]
      exact hu'
  have hopen : IsOpen ((extChartAt (modelWithCornersSelf ℂ ℂ) b).symm ≫
      extChartAt (modelWithCornersSelf ℂ ℂ) a).source := by
    rw [ext_coord_change_source, mcs_self_coe, Set.image_id]
    exact ((chartAt ℂ b).symm ≫ₕ (chartAt ℂ a)).open_source
  refine Filter.eventually_of_mem (hopen.mem_nhds hmem) ?_
  intro z hz
  simp only [Function.comp_apply]
  have hz' : (chartAt ℂ b).symm z ∈ (chartAt ℂ a).source := by
    rw [PartialEquiv.trans_source] at hz
    obtain ⟨-, hz2⟩ := hz
    simp only [Set.mem_preimage] at hz2
    rwa [extChartAt_self_coe_symm, extChartAt_source] at hz2
  rw [(chartAt ℂ a).left_inv hz']

/-! ### The main statement -/

theorem analyticAt_pullback_iff_chart {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {f : X → ℂ} {x y : X}
    (hxy : x ∈ (chartAt ℂ y).source) :
    AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ↔
      AnalyticAt ℂ (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  constructor
  · intro hf
    have hg : AnalyticAt ℂ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
      analyticAt_chart_transition hxy (mem_chart_source ℂ x)
    have hgy : ((chartAt ℂ x) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) = (chartAt ℂ x) x := by
      simp only [Function.comp_apply]
      rw [(chartAt ℂ y).left_inv hxy]
    have hcomp : AnalyticAt ℂ
        ((f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm)) ((chartAt ℂ y) x) :=
      hf.comp_of_eq hg hgy
    exact hcomp.congr (chart_eventuallyEq hxy (mem_chart_source ℂ x) f).symm
  · intro hf
    have hg : AnalyticAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
      analyticAt_chart_transition (mem_chart_source ℂ x) hxy
    have hgy : ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = (chartAt ℂ y) x := by
      simp only [Function.comp_apply]
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    have hcomp : AnalyticAt ℂ
        ((f ∘ (chartAt ℂ y).symm) ∘ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)) ((chartAt ℂ x) x) :=
      hf.comp_of_eq hg hgy
    exact hcomp.congr (chart_eventuallyEq (mem_chart_source ℂ x) hxy f).symm

end Commons.Geometry.Manifold