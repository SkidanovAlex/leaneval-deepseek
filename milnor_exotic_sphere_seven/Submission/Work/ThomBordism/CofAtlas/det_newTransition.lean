import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Structure
import Submission.Work.ThomBordism.CofAtlas.lvlExt_eventuallyEq_transAux
import Submission.Work.ThomBordism.PosAtlas.differentiableAt_extendCoordChange_isInvertible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The determinant of the transition between the corrected charts

`Work.ThomBordism.levelSet_positiveAtlas_of_coframing` needs the positivity of the transition
determinants of the corrected atlas `newChartedSpace D` built in `CofAtlas.Structure`.  Since the
corrected chart at `x` is the `Lvl` chart at `x`, post-composed with the reflection `reflectMap x`
exactly when the sign `flipSign x` is `-1`, its extended chart is

  `(D.newChart x).extend (𝓡∂ 9) = (reflectLin D x) ∘ (D.lvlExt x)`

(`newChart_extend_apply`), and correspondingly for the inverse on the half-space `{0 ≤ w 0}`
(`newChart_extend_symm_apply`).  The transition of two corrected charts is therefore the transition
of the two `Lvl` charts conjugated by the two linear reflections, whose determinant is the product
of the two signs.  This file proves that identity:

  `det (fderiv (transition)) = flipSign x * flipSign y * det (fderiv (transAux x y))`.

-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

/-! ## Elementary facts about the reflection -/

theorem reflLin_involutive (v : EuclideanSpace ℝ (Fin 9)) : reflLin (reflLin v) = v := by
  rw [reflLin_apply, reflLin_apply,
    ContinuousLinearEquiv.apply_symm_apply, reflCoordFun_involutive,
    ContinuousLinearEquiv.symm_apply_apply]

theorem reflectLin_self (D : Cof k n M) (x : D.S.Pre) (v : EuclideanSpace ℝ (Fin 9)) :
    reflectLin D x (reflectLin D x v) = v := by
  by_cases h : D.flipBool x
  · rw [reflectLin_of_flip D x h]
    exact reflLin_involutive v
  · rw [reflectLin_of_not_flip D x (Bool.eq_false_iff.mpr h)]
    rfl

/-! ## The extended chart of the corrected chart -/

/-- The extended chart of the corrected chart at `x` is the reflection composed with the extended
`Lvl` chart at `x`. -/
theorem newChart_extend_apply (D : Cof k n M) (x : D.S.Pre) (z : D.S.Pre) :
    ((D.newChart x).extend (𝓡∂ 9)) z = reflectLin D x ((D.lvlExt x) z) := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, newChart_apply,
    Cof.lvlExt, OpenPartialHomeomorph.extend_coe, Function.comp_apply, reflectMap_coord]

/-- On the half-space `{0 ≤ w 0}` (more precisely, whenever this point lies in the range of the
model) the inverse of the extended chart of the corrected chart at `x` is the inverse of the
extended `Lvl` chart at `x`, composed with the reflection. -/
theorem newChart_extend_symm_apply (D : Cof k n M) (x : D.S.Pre)
    {w : EuclideanSpace ℝ (Fin 9)} (hw : 0 ≤ w 0) :
    ((D.newChart x).extend (𝓡∂ 9)).symm w = (D.lvlExt x).symm (reflectLin D x w) := by
  rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, newChart_symm_apply,
    Cof.lvlExt, OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply]
  congr 1
  rw [reflectMap_apply, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hw]
  refine Subtype.ext ?_
  have h : 0 ≤ (reflectLin D x w) 0 := by rw [reflectLin_coord_zero]; exact hw
  rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le h]

/-! ## The positivity of the `Lvl` chart coordinate -/

/-- The chart coordinate of an interior point is strictly positive. -/
private theorem chartFun_coord_pos_aux (D : Cof k n M) (x : D.S.Pre) {q : D.S.Pre}
    (hq : q ∈ D.src x) (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    0 < (D.S.chartFun x q) 0 := by
  have hxcs : q ∈ D.S.chartSource x := D.src_subset_chartSource x hq
  have hnonneg : 0 ≤ (D.S.chartFun x q) 0 :=
    Work.PTGeometric.Lvl.Setup.chartFun_coord_nonneg D.S x hxcs
  refine lt_of_le_of_ne hnonneg (Ne.symm ?_)
  intro h0
  rcases Classical.em (x.1 ∈ (𝓡∂ (NN k)).boundary M) with hxb | hxb
  · have hz0 : ((D.domExt x) (q : M)).ofLp 0 = 0 := by
      rw [show D.domExt x (q : M) = D.S.chartHmap x (D.S.chartFun x q) from
          (Work.PTGeometric.Lvl.Setup.chartHmap_chartFun D.S x hxcs).symm,
        Work.PTGeometric.Lvl.Setup.chartHmap_coord_boundary D.S x hxb]
      exact h0
    have hbd : (q : M) ∈ (𝓡∂ (NN k)).boundary M :=
      (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
        (m := NN k) (Work.PTGeometric.Lvl.Setup.domChartAt_mem_maximalAtlas D.S x)
        hxcs.1).mpr hz0
    have hnotint : ¬ (𝓡∂ (NN k)).IsInteriorPoint (q : M) :=
      (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint (q : M)).mp hbd
    exact hnotint hint
  · set z : ModN k := (D.S.domChartAt x).extend (𝓡∂ (NN k)) (q : M) with hzdef
    have hball : ‖z - D.S.chartZ x‖ < D.S.chartRho x := by
      have hmem : z ∈ Metric.ball (D.S.chartZ x) (D.S.chartRho x) := hxcs.2.1.2
      rwa [Metric.mem_ball, dist_eq_norm] at hmem
    have hcoord : -‖D.S.chartBeta x (z - D.S.chartZ x)‖
        ≤ (D.S.chartBeta x (z - D.S.chartZ x)) 0 := by
      have h1 : |(D.S.chartBeta x (z - D.S.chartZ x)) 0|
          ≤ ‖D.S.chartBeta x (z - D.S.chartZ x)‖ := by
        simpa using PiLp.norm_apply_le (D.S.chartBeta x (z - D.S.chartZ x)) (0 : Fin 9)
      linarith [(abs_le.mp h1).1]
    have hbound : ‖D.S.chartBeta x (z - D.S.chartZ x)‖
        ≤ ‖D.S.chartBeta x‖ * D.S.chartRho x := by
      calc ‖D.S.chartBeta x (z - D.S.chartZ x)‖
          ≤ ‖D.S.chartBeta x‖ * ‖z - D.S.chartZ x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖D.S.chartBeta x‖ * D.S.chartRho x :=
            mul_le_mul_of_nonneg_left hball.le (norm_nonneg _)
    have h0' : (D.S.chartBeta x (z - D.S.chartZ x)) 0 + D.S.chartEps x = 0 := by
      have h := h0
      rw [show D.S.chartFun x q
            = D.S.chartBeta x (z - D.S.chartZ x) + D.S.chartEps x • Work.Surgery.e₀ 8 from rfl,
        PiLp.add_apply, PiLp.smul_apply, Work.Surgery.e₀_apply_zero, smul_eq_mul, mul_one] at h
      simpa using h
    have hE : D.S.chartEps x = ‖D.S.chartBeta x‖ * D.S.chartRho x + 1 := by
      rw [Work.PTGeometric.Lvl.Setup.chartEps, dif_neg hxb]
    have heps : 0 < ‖D.S.chartBeta x‖ * D.S.chartRho x + 1 := by
      have h1 : 0 < D.S.chartRho x := Work.PTGeometric.Lvl.Setup.chartRho_pos D.S x
      have h2 : 0 ≤ ‖D.S.chartBeta x‖ := norm_nonneg _
      nlinarith [mul_nonneg h2 h1.le]
    nlinarith [hcoord, hbound, hE, h0', heps]

/-- The extended `Lvl` chart of an interior point `q` has positive `0`-th coordinate. -/
theorem lvlExt_coord_pos (D : Cof k n M) (x : D.S.Pre) (hxi : (x : M) ∉ (𝓡∂ (NN k)).boundary M)
    {q : D.S.Pre} (hq : q ∈ D.src x) : 0 < (D.lvlExt x q) 0 := by
  have hqcs : q ∈ D.S.chartSource x := D.src_subset_chartSource x hq
  have hqint : (q : M) ∈ (𝓡∂ (NN k)).interior M :=
    D.interior_of_mem_intSrc x hxi (D.src_subset_intSrc x hq)
  have hval : D.lvlExt x q = D.S.chartFun x q := by
    rw [Cof.lvlExt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      Work.PTGeometric.Lvl.Setup.chartAt_apply_of_mem D.S x hqcs,
      modelWithCornersEuclideanHalfSpace_apply]
  rw [hval]
  exact chartFun_coord_pos_aux D x hq hqint

/-! ## The eventual equality of the transition with the conjugated `transAux` -/

theorem newChartTransition_eventuallyEq (D : Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x) (hy : q ∈ D.S.chartSource y)
    (hpos : 0 < (D.lvlExt x q) 0) :
    Filter.EventuallyEq (𝓝 ((reflectLin D x) (D.lvlExt x q)))
      (fun w : EuclideanSpace ℝ (Fin 9) =>
        ((D.newChart y).extend (𝓡∂ 9)) (((D.newChart x).extend (𝓡∂ 9)).symm w))
      (fun w => (reflectLin D y) (D.S.transAux x y ((reflectLin D x) w))) := by
  have hL4 := lvlExt_eventuallyEq_transAux D x y hx hy hpos
  have hz₀ : ((reflectLin D x) (D.lvlExt x q)) 0 = (D.lvlExt x q) 0 := by
    rw [reflectLin_coord_zero]
  have hnonneg : {w : EuclideanSpace ℝ (Fin 9) | 0 ≤ w 0} ∈ 𝓝 ((reflectLin D x) (D.lvlExt x q)) := by
    have hopen : IsOpen {w : EuclideanSpace ℝ (Fin 9) | 0 < w 0} :=
      isOpen_lt continuous_const (by fun_prop)
    have hmem : ((reflectLin D x) (D.lvlExt x q)) ∈ {w : EuclideanSpace ℝ (Fin 9) | 0 < w 0} := by
      rw [Set.mem_setOf_eq, hz₀]; exact hpos
    refine mem_of_superset (hopen.mem_nhds hmem) ?_
    intro w hw
    rw [Set.mem_setOf_eq] at hw ⊢
    exact le_of_lt hw
  have hcont : Filter.Tendsto (fun w : EuclideanSpace ℝ (Fin 9) => (reflectLin D x) w)
      (𝓝 ((reflectLin D x) (D.lvlExt x q))) (𝓝 ((reflectLin D x) ((reflectLin D x) (D.lvlExt x q)))) :=
    (reflectLin D x).continuous.continuousAt
  rw [reflectLin_self D x (D.lvlExt x q)] at hcont
  have h12 : ∀ᶠ w in 𝓝 ((reflectLin D x) (D.lvlExt x q)),
      D.lvlExt y ((D.lvlExt x).symm ((reflectLin D x) w)) = D.S.transAux x y ((reflectLin D x) w) :=
    hcont hL4
  refine (h12.and hnonneg).mono ?_
  rintro w ⟨hw12, hw0⟩
  show ((D.newChart y).extend (𝓡∂ 9)) (((D.newChart x).extend (𝓡∂ 9)).symm w)
      = (reflectLin D y) (D.S.transAux x y ((reflectLin D x) w))
  rw [newChart_extend_apply, newChart_extend_symm_apply D x hw0]
  exact congrArg (reflectLin D y) hw12

/-! ## The determinant of the corrected transition -/

theorem det_newTransition
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.src x) (hy : q ∈ D.src y)
    (hxi : (x : M) ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M)
    (hyi : (y : M) ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M)
    (hnex : D.flipSign x ≠ 0) (hney : D.flipSign y ≠ 0) :
    letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
      Work.ThomBordism.CofAtlas.newChartedSpace D
    LinearMap.det (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 9) =>
        (extChartAt (modelWithCornersEuclideanHalfSpace 9) y)
          ((extChartAt (modelWithCornersEuclideanHalfSpace 9) x).symm w))
      ((Work.ThomBordism.CofAtlas.reflectLin D x) ((D.lvlExt x) q))).toLinearMap
      = (D.flipSign x : ℝ) * (D.flipSign y : ℝ) *
        LinearMap.det (fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)).toLinearMap := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre := newChartedSpace D
  have hqcx : q ∈ D.S.chartSource x := D.src_subset_chartSource x hx
  have hqcy : q ∈ D.S.chartSource y := D.src_subset_chartSource y hy
  have hpos : 0 < (D.lvlExt x q) 0 := lvlExt_coord_pos D x hxi hx
  -- reformulate the goal in terms of the extended corrected charts
  show LinearMap.det (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 9) =>
        ((D.newChart y).extend (𝓡∂ 9)) (((D.newChart x).extend (𝓡∂ 9)).symm w))
      ((reflectLin D x) ((D.lvlExt x) q))).toLinearMap
      = (D.flipSign x : ℝ) * (D.flipSign y : ℝ) *
        LinearMap.det (fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)).toLinearMap
  -- switch to the `Lvl` instances for the differentiability statement
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre := Lvl.Setup.instChartedSpace (S := D.S)
  haveI : IsManifold (𝓡∂ 9) ∞ D.S.Pre := Lvl.Setup.instIsManifold (S := D.S)
  -- the eventual equality of the transition with the conjugated `transAux`
  have hev := newChartTransition_eventuallyEq D x y hqcx hqcy hpos
  -- differentiability of `transAux` at the point
  have hzsrc : D.lvlExt x q ∈
      ((𝓡∂ 9).extendCoordChange (D.lvlChart x) (D.lvlChart y)).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter (I := 𝓡∂ 9) (D.lvlChart x) (D.lvlChart y)]
    exact ⟨q, ⟨hqcx, hqcy⟩, rfl⟩
  have hzint : D.lvlExt x q ∈ interior (Set.range (𝓡∂ 9)) := by
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    exact hpos
  have hΦdiff : DifferentiableAt ℝ
      (⇑((𝓡∂ 9).extendCoordChange (D.lvlChart x) (D.lvlChart y))) (D.lvlExt x q) :=
    (Work.ThomBordism.PosAtlas.differentiableAt_extendCoordChange_isInvertible
      (I := 𝓡∂ 9) (n := ∞) (D.lvlChart x) (D.lvlChart y)
      (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas y)
      (by norm_num) hzsrc hzint).1
  have hTdiff : DifferentiableAt ℝ (D.S.transAux x y) (D.lvlExt x q) :=
    (lvlExt_eventuallyEq_transAux D x y hqcx hqcy hpos).differentiableAt_iff |>.mp hΦdiff
  -- the chain rule
  have hchain : fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 9) =>
        (reflectLin D y) (D.S.transAux x y ((reflectLin D x) w)))
      ((reflectLin D x) (D.lvlExt x q))
      = (reflectLin D y).comp ((fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)).comp
          (reflectLin D x)) := by
    have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 9) => (reflectLin D x) w)
        (reflectLin D x) ((reflectLin D x) (D.lvlExt x q)) :=
      ContinuousLinearMap.hasFDerivAt (reflectLin D x)
    have h2 : HasFDerivAt (D.S.transAux x y)
        (fderiv ℝ (D.S.transAux x y) (D.lvlExt x q))
        ((reflectLin D x) ((reflectLin D x) (D.lvlExt x q))) := by
      rw [reflectLin_self D x (D.lvlExt x q)]
      exact hTdiff.hasFDerivAt
    have h3 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 9) =>
          D.S.transAux x y ((reflectLin D x) w))
        ((fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)).comp (reflectLin D x))
        ((reflectLin D x) (D.lvlExt x q)) :=
      h2.comp ((reflectLin D x) (D.lvlExt x q)) h1
    exact ((ContinuousLinearMap.hasFDerivAt (reflectLin D y)).comp
      ((reflectLin D x) (D.lvlExt x q)) h3).fderiv
  rw [hev.fderiv_eq, hchain]
  rw [show ((reflectLin D y).comp ((fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)).comp
        (reflectLin D x))).toLinearMap
      = ((reflectLin D y).toLinearMap).comp
        (((fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)).toLinearMap).comp
          ((reflectLin D x).toLinearMap)) from rfl]
  rw [LinearMap.det_comp, LinearMap.det_comp, reflectLin_det D x hnex, reflectLin_det D y hney]
  ring

end

end Work.ThomBordism.CofAtlas
