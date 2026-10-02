import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The graph data of a plane, and inversion of the chart

This file proves the linear algebra behind the charts of the oriented Grassmannian:

* the matrix `frameMatrix S f` is invertible exactly when the `S`-projection is *injective* on the
  plane of `f` (`frameMatrix_det_ne_zero_iff`), which is a condition on the plane only
  (`frameMatrix_det_ne_zero_of_span_eq`);
* hence the Gram–Schmidt frame of a graph lies in the chart `S` (`graphFrame_mem_chartSet`,
  `graphPoint_mem_baseSet`);
* two frames of the same plane give the same coordinate evaluation (`coordEval_eq_of_span_eq`) and
  the same chart data (`chartData_eq_of_span_eq`);
* the two round trips: `coordEval S (graphFrame S d) v = graphMap S d v` and
  `chartData S (graphPoint S d) = d`.
-/

namespace Work.ThomBordism.Grassmann.Smooth

open scoped Topology
open Set

noncomputable section

variable {k m : ℕ}

/-! ## Coordinates of a linear combination of a plain family -/

theorem coeffMap_eq_ofLpCLM (f : Fin k → Amb (k + m)) (c : Fin k → ℝ) :
    coeffMap f c = ofLpCLM (k + m) (∑ i, c i • f i) := by
  funext x
  rw [coeffMap_apply, ofLpCLM_apply, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, EuclideanSpace.coe_proj]

/-- `coordProj S` and `projS S` are the same map, read with or without the `WithLp` transfer. -/
theorem coordProj_ofLpCLM (S : ChartIdx k m) (w : Amb (k + m)) :
    coordProj S (ofLpCLM (k + m) w) = ofLpCLM k (projS S w) := by
  funext i
  rw [coordProj_apply, ofLpCLM_apply, ofLpCLM_apply]
  rfl

/-- Reading `projS S w` back as the `S`-coordinates of `w`. -/
theorem projS_eq_toLp_coordProj (S : ChartIdx k m) (w : Amb (k + m)) :
    projS S w = WithLp.toLp 2 (coordProj S (WithLp.ofLp w)) := by
  apply WithLp.ofLp_injective
  funext i
  rw [WithLp.ofLp_toLp, projS_apply_amb]
  rfl

/-! ## Invertibility of the frame matrix -/

/-- **`frameMatrix S f` is invertible if and only if the `S`-projection is injective on the plane
of `f`** (for a linearly independent family `f`). -/
theorem frameMatrix_det_ne_zero_iff (S : ChartIdx k m) {f : Fin k → Amb (k + m)}
    (hli : LinearIndependent ℝ f) :
    (frameMatrix S f).det ≠ 0 ↔
      ∀ v : Amb (k + m), v ∈ Submodule.span ℝ (Set.range f) → projS S v = 0 → v = 0 := by
  have hkey : ∀ c : Fin k → ℝ,
      (Matrix.toLin' (frameMatrix S f)) c = coordProj S (coeffMap f c) := by
    intro c; rw [toLin'_frameMatrix]; rfl
  have hofLp : ∀ x : Amb k, ofLpCLM k x = 0 → x = 0 := by
    intro x hx
    apply WithLp.ofLp_injective
    funext i
    have := congrFun hx i
    simpa [ofLpCLM_apply] using this
  constructor
  · intro hdet v hv hv0
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
    have hker : (Matrix.toLin' (frameMatrix S f)).ker = ⊥ := by
      by_contra hne
      have h0 : (frameMatrix S f).det = 0 :=
        (LinearMap.det_toLin' (frameMatrix S f)).symm.trans
          ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hne)
      exact hdet h0
    have hc1 : (Matrix.toLin' (frameMatrix S f)) c = 0 := by
      rw [hkey, coeffMap_eq_ofLpCLM, coordProj_ofLpCLM, hc, hv0, map_zero]
    have hc0 : c = 0 := LinearMap.ker_eq_bot.mp hker (by simpa using hc1)
    rw [← hc, hc0]
    simp
  · intro hinj
    by_contra hdet
    have hker : (Matrix.toLin' (frameMatrix S f)).ker ≠ ⊥ := by
      have h0 : (frameMatrix S f).det = 0 := hdet
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot).mp (by rwa [LinearMap.det_toLin'])
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hker
    have h1 : coordProj S (coeffMap f c) = 0 := by
      have := hc; rwa [LinearMap.mem_ker, hkey] at this
    have h2 : projS S (∑ i, c i • f i) = 0 := by
      refine hofLp _ ?_
      rw [← coordProj_ofLpCLM, ← coeffMap_eq_ofLpCLM]
      exact h1
    have h3 : (∑ i, c i • f i) = 0 :=
      hinj _ (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) h2
    exact hc0 (funext ((Fintype.linearIndependent_iff.mp hli) c h3))

/-- **The invertibility of the frame matrix depends only on the plane.** -/
theorem frameMatrix_det_ne_zero_of_span_eq (S : ChartIdx k m) {f g : Fin k → Amb (k + m)}
    (hli : LinearIndependent ℝ f) (hli' : LinearIndependent ℝ g)
    (hspan : Submodule.span ℝ (Set.range f) = Submodule.span ℝ (Set.range g))
    (hf : (frameMatrix S f).det ≠ 0) : (frameMatrix S g).det ≠ 0 := by
  rw [frameMatrix_det_ne_zero_iff S hli'] at ⊢
  intro v hv hv0
  exact (frameMatrix_det_ne_zero_iff S hli).mp hf v (hspan ▸ hv) hv0

/-- The determinant of the `S`-matrix of the Gram–Schmidt frame of a graph does not vanish. -/
theorem graphFrame_det_ne_zero (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (frameMatrix S (graphFrame S d)).det ≠ 0 := by
  have hf : (frameMatrix S (graphVec S d)).det ≠ 0 := by
    rw [frameMatrix_graphVec, Matrix.det_one]; exact one_ne_zero
  have hspan : Submodule.span ℝ (Set.range (graphVec S d))
      = Submodule.span ℝ (Set.range (graphFrame S d)) := (span_graphFrame_eq S d).symm
  exact frameMatrix_det_ne_zero_of_span_eq S (linearIndependent_graphVec S d)
    (orthonormal_graphFrame S d).linearIndependent hspan hf

/-- The Gram–Schmidt frame of a graph lies in the chart `S`. -/
theorem graphFrame_mem_chartSet (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (⟨graphFrame S d, orthonormal_graphFrame S d⟩ : Stiefel k m) ∈ chartSet S :=
  graphFrame_det_ne_zero S d

/-- The graph point lies in the chart `S`. -/
theorem graphPoint_mem_baseSet (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    graphPoint S d ∈ baseSet S :=
  (mem_baseSet_iff S _).mpr (graphFrame_mem_chartSet S d)

/-! ## The chart data depends only on the plane -/

theorem coordVec_eq_of_span_eq {S : ChartIdx k m} {f g : Stiefel k m}
    (hf : f ∈ chartSet S) (hg : g ∈ chartSet S)
    (hspan : Submodule.span ℝ (Set.range f.1) = Submodule.span ℝ (Set.range g.1)) (i : Fin k) :
    coordVec S f i = coordVec S g i := by
  refine eq_of_mem_span_of_coordinates_eq (f := g.1) ((mem_chartSet S g).mp hg) ?_ ?_ ?_
  · rw [← hspan]; exact coordVec_mem_span S f i
  · exact coordVec_mem_span S g i
  · intro l
    have h1 : coordVec S f i (idxS S l) = ((Pi.single i (1 : ℝ)) : Fin k → ℝ) l := by
      rw [← projS_apply_amb S (coordVec S f i) l, projS_eq_toLp_coordProj]
      exact congrFun (coordProj_coordVec S f i hf) l
    have h2 : coordVec S g i (idxS S l) = ((Pi.single i (1 : ℝ)) : Fin k → ℝ) l := by
      rw [← projS_apply_amb S (coordVec S g i) l, projS_eq_toLp_coordProj]
      exact congrFun (coordProj_coordVec S g i hg) l
    rw [h1, h2]

theorem coordEval_eq_of_span_eq {S : ChartIdx k m} {f g : Stiefel k m}
    (hf : f ∈ chartSet S) (hg : g ∈ chartSet S)
    (hspan : Submodule.span ℝ (Set.range f.1) = Submodule.span ℝ (Set.range g.1)) :
    coordEval S f = coordEval S g := by
  funext v
  rw [coordEval, coordEval]
  exact Finset.sum_congr rfl fun i _ => by rw [coordVec_eq_of_span_eq hf hg hspan i]

theorem coordEvalCLM_eq_of_span_eq {S : ChartIdx k m} {f g : Stiefel k m}
    (hf : f ∈ chartSet S) (hg : g ∈ chartSet S)
    (hspan : Submodule.span ℝ (Set.range f.1) = Submodule.span ℝ (Set.range g.1)) :
    coordEvalCLM S f.1 = coordEvalCLM S g.1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [coordEvalCLM_stiefel_apply, coordEvalCLM_stiefel_apply,
    congrFun (coordEval_eq_of_span_eq hf hg hspan) v]

/-- **Two frames of the same plane give the same chart data.** -/
theorem chartData_eq_of_span_eq {S : ChartIdx k m} {f g : Stiefel k m}
    (hf : f ∈ chartSet S) (hg : g ∈ chartSet S)
    (hspan : Submodule.span ℝ (Set.range f.1) = Submodule.span ℝ (Set.range g.1)) :
    chartData S (Quotient.mk'' f) = chartData S (Quotient.mk'' g) := by
  rw [chartData_mk, chartData_mk, chartFun, chartFun, coordEvalCLM_eq_of_span_eq hf hg hspan]

/-! ## The round trips -/

/-- The `S`-coordinate evaluation of the Gram–Schmidt frame of a graph is the graph map. -/
theorem coordEval_graphFrame (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) (v : Amb k) :
    coordEval S ⟨graphFrame S d, orthonormal_graphFrame S d⟩ v = graphMap S d v := by
  refine eq_of_mem_span_of_coordinates_eq (f := graphFrame S d)
    (frameMatrix_det_ne_zero_of_span_eq S (linearIndependent_graphVec S d)
      (orthonormal_graphFrame S d).linearIndependent (span_graphFrame_eq S d).symm
      (by rw [frameMatrix_graphVec, Matrix.det_one]; exact one_ne_zero)) ?_ ?_ ?_
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (coordVec_mem_span S ⟨graphFrame S d, orthonormal_graphFrame S d⟩ i)
  · exact graphMap_mem_span_graphFrame S d v
  · intro l
    have h1 : coordEval S ⟨graphFrame S d, orthonormal_graphFrame S d⟩ v (idxS S l)
        = (WithLp.ofLp v) l := by
      rw [← projS_apply_amb S _ l, projS_eq_toLp_coordProj]
      exact congrFun (coordProj_coordEval S _ v (graphFrame_mem_chartSet S d)) l
    have h2 : graphMap S d v (idxS S l) = (WithLp.ofLp v) l := by
      rw [← projS_apply_amb S (graphMap S d v) l, projS_graphMap]
    rw [h1, h2]

/-- **The chart data of the graph point of `d` is `d`.** -/
theorem chartData_graphPoint (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    chartData S (graphPoint S d) = d := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [show graphPoint S d
      = Quotient.mk'' (⟨graphFrame S d, orthonormal_graphFrame S d⟩ : Stiefel k m) from rfl,
    chartData_mk_apply, coordEval_graphFrame S d v]
  exact projC_graphMap S d v

end

end Work.ThomBordism.Grassmann.Smooth
