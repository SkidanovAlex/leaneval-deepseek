import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.Transition
import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.contDiffOn_graphChange
import Submission.Work.Model.prod_transfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The smooth atlas of the oriented Grassmannian

The charts `chart S ε` cover `OG k m` and their transitions are smooth, so `OG k m` is a smooth
manifold modelled on `Amb k →L[ℝ] Amb m`.
-/

namespace Work.ThomBordism.Grassmann.Smooth

open scoped Topology ContDiff Manifold
open Set

noncomputable section

variable {k m : ℕ}

/-- The index type of the atlas of the oriented Grassmannian: a chart index together with an
orientation sign. -/
abbrev AtlasIdx (k m : ℕ) := ChartIdx k m × ℝ

/-- The atlas of the oriented Grassmannian. -/
def atlas (k m : ℕ) : Set (OpenPartialHomeomorph (OG k m) (Amb k →L[ℝ] Amb m)) :=
  Set.range (fun i : AtlasIdx k m => chart i.1 i.2)

theorem chart_mem_atlas (S : ChartIdx k m) (ε : ℝ) : chart S ε ∈ atlas k m := ⟨(S, ε), rfl⟩

theorem exists_mem_chartSrc (x : OG k m) : ∃ i : AtlasIdx k m, x ∈ (chart i.1 i.2).source := by
  obtain ⟨S, hS⟩ := exists_mem_baseSet x
  exact ⟨(S, frameSign S x), hS, rfl⟩

instance instChartedSpaceOG (k m : ℕ) :
    ChartedSpace (Amb k →L[ℝ] Amb m) (OG k m) where
  atlas := atlas k m
  chartAt x := chart (Classical.choose (exists_mem_chartSrc x)).1
    (Classical.choose (exists_mem_chartSrc x)).2
  mem_chart_source x := Classical.choose_spec (exists_mem_chartSrc x)
  chart_mem_atlas x := ⟨Classical.choose (exists_mem_chartSrc x), rfl⟩

/-! ## Smoothness of the transitions -/

/-- The transition map of the charts `S` and `T`, written as a function of the graph data. -/
theorem contDiffOn_chartInv_chartData (S T : ChartIdx k m) (ε ε' : ℝ) :
    ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun d : Amb k →L[ℝ] Amb m => chartData T (chartInv S ε d))
      {d | chartInv S ε d ∈ chartSrc S ε ∩ chartSrc T ε'} := by
  have hsub : ∀ d, chartInv S ε d ∈ chartSrc S ε ∩ chartSrc T ε' → graphUnit S T d := by
    intro d hd
    have hdTgt : d ∈ chartTgt S ε := hd.1
    obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = chartInv S ε d :=
      Quotient.exists_rep (chartInv S ε d)
    have hfS : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hf ▸ hd.1.1)
    have hfT : f ∈ chartSet T := (mem_baseSet_iff T f).mp (hf ▸ hd.2.1)
    have hfd : chartFun S f = d := by
      rw [← chartData_mk S f, hf, chartData_chartInv S ε hdTgt]
    exact graphUnit_of_chartFun_eq hfS hfT hfd
  have hcd : ContDiffOn ℝ (∞ : ℕ∞ω) (graphChange S T)
      {d | chartInv S ε d ∈ chartSrc S ε ∩ chartSrc T ε'} :=
    (Work.ThomBordism.Grassmann.Smooth.Chart.contDiffOn_graphChange S T).mono hsub
  refine hcd.congr ?_
  intro d hd
  exact chartData_chartInv_eq_graphChange S T ε hd.1 hd.2.1

theorem chart_trans_source (S T : ChartIdx k m) (ε ε' : ℝ) :
    ((chart S ε).symm ≫ₕ (chart T ε')).source
      = {d | chartInv S ε d ∈ chartSrc S ε ∩ chartSrc T ε'} := by
  rw [OpenPartialHomeomorph.trans_source]
  rfl

theorem chart_trans_apply (S T : ChartIdx k m) (ε ε' : ℝ) :
    ⇑((chart S ε).symm ≫ₕ (chart T ε'))
      = fun d : Amb k →L[ℝ] Amb m => chartData T (chartInv S ε d) := by
  funext d
  rw [OpenPartialHomeomorph.trans_apply]
  rfl

theorem chart_trans_symm_apply (S T : ChartIdx k m) (ε ε' : ℝ) :
    ⇑((chart S ε).symm ≫ₕ (chart T ε')).symm
      = fun d : Amb k →L[ℝ] Amb m => chartData S (chartInv T ε' d) := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  exact chart_trans_apply T S ε' ε

theorem chart_trans_target (S T : ChartIdx k m) (ε ε' : ℝ) :
    ((chart S ε).symm ≫ₕ (chart T ε')).target
      = {d | chartInv T ε' d ∈ chartSrc T ε' ∩ chartSrc S ε} := by
  rw [OpenPartialHomeomorph.trans_target]
  rfl

/-- **The transition between two charts of the oriented Grassmannian is smooth.** -/
theorem chart_symm_trans_chart_mem (S : ChartIdx k m) (T : ChartIdx k m) (ε ε' : ℝ) :
    (chart S ε).symm ≫ₕ (chart T ε') ∈ contDiffGroupoid ∞ (𝓘(ℝ, Amb k →L[ℝ] Amb m)) := by
  rw [Work.Model.mem_contDiffGroupoid_self_iff]
  constructor
  · rw [chart_trans_source, chart_trans_apply]
    exact contDiffOn_chartInv_chartData S T ε ε'
  · rw [chart_trans_target, chart_trans_symm_apply]
    exact contDiffOn_chartInv_chartData T S ε' ε

/-- **The oriented Grassmannian is a smooth manifold**, modelled on `Amb k →L[ℝ] Amb m`. -/
instance instIsManifoldOG (k m : ℕ) :
    IsManifold (𝓘(ℝ, Amb k →L[ℝ] Amb m)) (∞ : ℕ∞ω) (OG k m) where
  compatible := by
    intro e e' he he'
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := he'
    exact chart_symm_trans_chart_mem i.1 j.1 i.2 j.2

end

end Work.ThomBordism.Grassmann.Smooth
