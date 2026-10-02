import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.ChartInv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The transition formula for the graph charts

The chart `chart T ε` of a point whose graph data in the chart `S` is `d` is given by the model
expression `graphChange S T d`: re-reading a graph in the chart `T` is the map
`c ↦ (projC T ∘ graphMap S c) ∘ (projS T ∘ graphMap S c)⁻¹`.
-/

namespace Work.ThomBordism.Grassmann.Smooth

open scoped Topology
open Set

noncomputable section

variable {k m : ℕ}

/-- The plane of a frame of the chart `S` with graph data `d` is the graph of `d`. -/
theorem graphMap_eq_coordEval {S : ChartIdx k m} {f : Stiefel k m} (hfS : f ∈ chartSet S)
    {d : Amb k →L[ℝ] Amb m} (hd : chartFun S f = d) (v : Amb k) :
    graphMap S d v = coordEval S f v := by
  have h1 : projS S (coordEval S f v) = v := projS_coordEval S f hfS v
  have h2 : projC S (coordEval S f v) = d v := by
    rw [← chartFun_apply]; exact DFunLike.congr_fun hd v
  calc graphMap S d v
      = inclS S (projS S (graphMap S d v)) + inclC S (projC S (graphMap S d v)) :=
        (inclS_projS_add_inclC_projC S _).symm
    _ = inclS S (projS S (coordEval S f v)) + inclC S (projC S (coordEval S f v)) := by
        rw [projS_graphMap, h1, projC_graphMap, h2]
    _ = coordEval S f v := inclS_projS_add_inclC_projC S _

/-- **The transition formula**: for a frame `f` of the chart `T` whose graph data in the chart `S`
is `d`, the graph data in the chart `T` is `graphChange S T d`. -/
theorem chartFun_eq_graphChange {S T : ChartIdx k m} {f : Stiefel k m}
    (hfS : f ∈ chartSet S) (hfT : f ∈ chartSet T) {d : Amb k →L[ℝ] Amb m}
    (hd : chartFun S f = d) :
    chartFun T f = graphChange S T d := by
  have hplane : ∀ v : Amb k, graphMap S d v ∈ Submodule.span ℝ (Set.range f.1) := by
    intro v
    rw [graphMap_eq_coordEval hfS hd v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (coordVec_mem_span S f i)
  have hspanT : ∀ v : Amb k, coordEval T f v ∈ Submodule.span ℝ (Set.range f.1) := by
    intro v
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (coordVec_mem_span T f i)
  -- the `T`-projection is injective on the plane
  have hsep : ∀ a b : Amb (k + m), a ∈ Submodule.span ℝ (Set.range f.1) →
      b ∈ Submodule.span ℝ (Set.range f.1) → projS T a = projS T b → a = b := by
    intro a b ha hb hab
    have hsub : a - b ∈ Submodule.span ℝ (Set.range f.1) := Submodule.sub_mem _ ha hb
    have h0 : projS T (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h := coordProj_injOn_span T f hfT hsub (Submodule.zero_mem _) ?_
    · exact sub_eq_zero.mp h
    rw [show (a - b).ofLp = ofLpCLM (k + m) (a - b) from rfl,
      show (0 : Amb (k + m)).ofLp = ofLpCLM (k + m) 0 from rfl,
      coordProj_ofLpCLM, coordProj_ofLpCLM, h0, map_zero]
    simp
  -- hence the graph change is a unit
  have hu : Function.Injective ((projS T).comp (graphMap S d)) := by
    intro v w hvw
    have h1 : projS T (graphMap S d (v - w)) = 0 := by
      calc projS T (graphMap S d (v - w))
          = projS T (graphMap S d v - graphMap S d w) := by rw [map_sub]
        _ = projS T (graphMap S d v) - projS T (graphMap S d w) := by rw [map_sub]
        _ = 0 := by
            rw [show projS T (graphMap S d v) = ((projS T).comp (graphMap S d)) v from rfl,
              show projS T (graphMap S d w) = ((projS T).comp (graphMap S d)) w from rfl,
              hvw, sub_self]
    have h2 : graphMap S d (v - w) = 0 :=
      hsep _ _ (hplane _) (Submodule.zero_mem _) (by rw [h1, map_zero])
    exact sub_eq_zero.mp (graphMap_injective S d (by rw [h2, map_zero]))
  have hunit : IsUnit ((projS T).comp (graphMap S d)) := by
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    exact ⟨hu, LinearMap.injective_iff_surjective.mp hu⟩
  refine ContinuousLinearMap.ext fun v => ?_
  rw [chartFun_apply, graphChange_apply]
  have hw : projS T (graphMap S d (Ring.inverse ((projS T).comp (graphMap S d)) v)) = v := by
    have h := congrFun (congrArg (fun U : Amb k →L[ℝ] Amb k => ⇑U)
      (Ring.mul_inverse_cancel ((projS T).comp (graphMap S d)) hunit)) v
    simpa using h
  have hcoord : coordEval T f v
      = graphMap S d (Ring.inverse ((projS T).comp (graphMap S d)) v) :=
    hsep _ _ (hspanT v) (hplane _) (by rw [projS_coordEval T f hfT v, hw])
  rw [← hcoord]

/-- The `T`-projection is invertible on the graph of the graph data of a frame of the chart `T`. -/
theorem graphUnit_of_chartFun_eq {S T : ChartIdx k m} {f : Stiefel k m}
    (hfS : f ∈ chartSet S) (hfT : f ∈ chartSet T) {d : Amb k →L[ℝ] Amb m}
    (hd : chartFun S f = d) : graphUnit S T d := by
  have hplane : ∀ v : Amb k, graphMap S d v ∈ Submodule.span ℝ (Set.range f.1) := by
    intro v
    rw [graphMap_eq_coordEval hfS hd v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (coordVec_mem_span S f i)
  have hu : Function.Injective ((projS T).comp (graphMap S d)) := by
    intro v w hvw
    have h1 : projS T (graphMap S d (v - w)) = 0 := by
      calc projS T (graphMap S d (v - w))
          = projS T (graphMap S d v - graphMap S d w) := by rw [map_sub]
        _ = projS T (graphMap S d v) - projS T (graphMap S d w) := by rw [map_sub]
        _ = 0 := by
            rw [show projS T (graphMap S d v) = ((projS T).comp (graphMap S d)) v from rfl,
              show projS T (graphMap S d w) = ((projS T).comp (graphMap S d)) w from rfl,
              hvw, sub_self]
    have h2 : graphMap S d (v - w) = 0 := by
      refine coordProj_injOn_span T f hfT (hplane _) (Submodule.zero_mem _) ?_
      rw [show (graphMap S d (v - w)).ofLp = ofLpCLM (k + m) (graphMap S d (v - w)) from rfl,
        show (0 : Amb (k + m)).ofLp = ofLpCLM (k + m) 0 from rfl,
        coordProj_ofLpCLM, coordProj_ofLpCLM, h1, map_zero]
      simp
    exact sub_eq_zero.mp (graphMap_injective S d (by rw [h2, map_zero]))
  show IsUnit ((projS T).comp (graphMap S d))
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨hu, LinearMap.injective_iff_surjective.mp hu⟩

/-- **The chart of the graph point with data `d`**: the point of the chart `S` with data `d` has
graph data `graphChange S T d` in the chart `T`. -/
theorem chartData_chartInv_eq_graphChange (S T : ChartIdx k m) (ε : ℝ) {d : Amb k →L[ℝ] Amb m}
    (hdS : d ∈ chartTgt S ε) (hdT : chartInv S ε d ∈ baseSet T) :
    chartData T (chartInv S ε d) = graphChange S T d := by
  obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = chartInv S ε d :=
    Quotient.exists_rep (chartInv S ε d)
  have hzS : chartInv S ε d ∈ chartSrc S ε := hdS
  have hfS : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hf ▸ hzS.1)
  have hfT : f ∈ chartSet T := (mem_baseSet_iff T f).mp (hf ▸ hdT)
  have hfd : chartFun S f = d := by
    rw [← chartData_mk S f, hf, chartData_chartInv S ε hdS]
  rw [← hf, chartData_mk, chartFun_eq_graphChange hfS hfT hfd]

end

end Work.ThomBordism.Grassmann.Smooth
