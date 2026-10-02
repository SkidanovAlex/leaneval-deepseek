import Submission.Work.PTGeometric.Lvl.KeyLemma

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chart of the local level set at a point

This is the copy of `Work.ThomBordism.Transversality.Preimage.Chart` for the local level-set data:
the chart at `w ∈ W` is built from the submersion normal form of the local defining function `g w`
at `w`.  In addition to the original conditions the source of the chart is restricted by the
requirement that the underlying point of `M` lies in the neighbourhood `U w` on which `g w`
cuts out `W`; this is what replaces the global "zero set of `coreMap` is the preimage" in the
transition and inverse-chart arguments.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold Topology ContDiff
open Function Set Manifold
open ModelWithCorners
open Classical
open Work.ThomBordism.Transversality.Preimage

namespace Work.PTGeometric

noncomputable section

namespace Lvl

namespace Setup

variable {k : ℕ} (S : Setup k)

noncomputable def chartT (w : S.Pre) : EuclideanSpace ℝ (Fin ((8 + k) + 1)) ≃L[ℝ]
    (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 9)) :=
  if h : w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M then
    Classical.choose (exists_linearEquiv_prod_coord 8 k (aLin S w) (aLin_surjective S w)
      (sLin (8 + k)) (exists_ker_coord_ne_zero S w h))
  else Classical.choose (exists_linearEquiv_prod_ker 8 k (aLin S w) (aLin_surjective S w))

theorem chartT_fst (w : S.Pre) : ∀ v : EuclideanSpace ℝ (Fin ((8 + k) + 1)),
    (chartT S w v).1 = aLin S w v := by
  intro v
  rw [chartT]
  split_ifs with h
  · exact (Classical.choose_spec (exists_linearEquiv_prod_coord 8 k (aLin S w)
      (aLin_surjective S w) (sLin (8 + k)) (exists_ker_coord_ne_zero S w h))).1 v
  · exact Classical.choose_spec (exists_linearEquiv_prod_ker 8 k (aLin S w)
      (aLin_surjective S w)) v

theorem chartT_snd_coord (w : S.Pre) (h : w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M) :
    ∀ v : EuclideanSpace ℝ (Fin ((8 + k) + 1)),
      aLin S w v = 0 → (chartT S w v).2 0 = sLin (8 + k) v := by
  intro v hv
  rw [chartT, dif_pos h]
  exact (Classical.choose_spec (exists_linearEquiv_prod_coord 8 k (aLin S w)
    (aLin_surjective S w) (sLin (8 + k)) (exists_ker_coord_ne_zero S w h))).2 v hv

/-- The second component of the splitting. -/
noncomputable def chartBeta (w : S.Pre) :
    EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin 9) :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin 9))).comp
    (chartT S w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ]
      (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 9)))

/-- The inverse of `chartBeta` on the kernel of `aLin w`. -/
noncomputable def chartIota (w : S.Pre) :
    EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
  ((chartT S w).symm : _ →L[ℝ] _).comp
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin 9)))

theorem chartBeta_apply (w : S.Pre) (v : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    chartBeta S w v = (chartT S w v).2 := rfl

theorem chartBeta_iota (w : S.Pre) (y : EuclideanSpace ℝ (Fin 9)) :
    chartBeta S w (chartIota S w y) = y := by
  simp [chartBeta, chartIota]

theorem chartIota_mem_ker (w : S.Pre) (y : EuclideanSpace ℝ (Fin 9)) :
    aLin S w (chartIota S w y) = 0 := by
  have h : chartT S w (chartIota S w y) = (0, y) := by
    simp [chartIota]
  rw [← chartT_fst S w (chartIota S w y), h]

theorem chartIota_beta (w : S.Pre) {v : EuclideanSpace ℝ (Fin ((8 + k) + 1))}
    (hv : aLin S w v = 0) : chartIota S w (chartBeta S w v) = v := by
  have h : chartT S w (chartIota S w (chartBeta S w v)) = chartT S w v := by
    rw [Prod.ext_iff]
    constructor
    · show (chartT S w (chartIota S w (chartBeta S w v))).1 = (chartT S w v).1
      rw [chartT_fst S w, chartT_fst S w, chartIota_mem_ker, hv]
    · show (chartT S w (chartIota S w (chartBeta S w v))).2 = (chartT S w v).2
      rw [show (chartT S w (chartIota S w (chartBeta S w v))).2
          = chartBeta S w (chartIota S w (chartBeta S w v)) from rfl, chartBeta_iota,
        chartBeta_apply]
  exact (chartT S w).injective h

theorem chartIota_coord (w : S.Pre) (h : w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M)
    (y : EuclideanSpace ℝ (Fin 9)) : (chartIota S w y) 0 = y 0 := by
  have h1 : (chartT S w (chartIota S w y)).2 0 = sLin (8 + k) (chartIota S w y) :=
    chartT_snd_coord S w h _ (chartIota_mem_ker S w y)
  have h2 : (chartT S w (chartIota S w y)).2 = y := by
    simp [chartIota]
  rw [h2] at h1
  rw [h1, sLin_apply]

/-- The normal-form coordinate of the base point. -/
noncomputable def chartZ (w : S.Pre) : EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
  (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) w.1

theorem chartZ_coord_nonneg (w : S.Pre) : 0 ≤ (chartZ S w) 0 :=
  zero_le_extend_apply_coord (S.domChartAt w) (mem_domChartAt_source S w)

theorem chartZ_coord_eq_zero (w : S.Pre) (h : w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M) :
    (chartZ S w) 0 = 0 :=
  (mem_boundary_iff_extend_apply_coord_eq_zero (m := (8 + k) + 1)
    (domChartAt_mem_maximalAtlas S w) (mem_domChartAt_source S w)).mp h

theorem chartZ_coord_pos (w : S.Pre) (h : w.1 ∉ (𝓡∂ ((8 + k) + 1)).boundary S.M) :
    0 < (chartZ S w) 0 := by
  refine lt_of_le_of_ne (chartZ_coord_nonneg S w) ?_
  intro h0
  exact h ((mem_boundary_iff_extend_apply_coord_eq_zero (m := (8 + k) + 1)
    (domChartAt_mem_maximalAtlas S w) (mem_domChartAt_source S w)).mpr h0.symm)

/-- The radius of the ball in which the chart is defined. -/
noncomputable def chartRho (w : S.Pre) : ℝ :=
  if h : w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M then 1
  else min 1 ((chartZ S w) 0 / 2)

theorem chartRho_pos (w : S.Pre) : 0 < chartRho S w := by
  rw [chartRho]
  split_ifs with h
  · exact one_pos
  · exact lt_min one_pos (half_pos (chartZ_coord_pos S w h))

theorem chartRho_le_one (w : S.Pre) : chartRho S w ≤ 1 := by
  rw [chartRho]
  split_ifs with h
  · exact le_rfl
  · exact min_le_left _ _

theorem chartRho_le_coord (w : S.Pre) (h : w.1 ∉ (𝓡∂ ((8 + k) + 1)).boundary S.M) :
    chartRho S w ≤ (chartZ S w) 0 / 2 := by
  rw [chartRho, dif_neg h]
  exact min_le_right _ _

/-- The additive constant of the chart: zero at boundary points of `M`, large enough elsewhere to
push the image into the interior of the half-space. -/
noncomputable def chartEps (w : S.Pre) : ℝ :=
  if h : w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M then 0
  else ‖chartBeta S w‖ * chartRho S w + 1

theorem chartEps_pos (w : S.Pre) (h : w.1 ∉ (𝓡∂ ((8 + k) + 1)).boundary S.M) :
    0 < chartEps S w := by
  rw [chartEps, dif_neg h]
  have h1 : 0 < chartRho S w := chartRho_pos S w
  have h2 : 0 ≤ ‖chartBeta S w‖ := norm_nonneg _
  nlinarith [mul_nonneg h2 h1.le]

theorem chartEps_eq_zero (w : S.Pre) (h : w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M) :
    chartEps S w = 0 := by
  rw [chartEps, dif_pos h]

/-- The open set of normal-form coordinates in which the chart is defined.  It consists of the
coordinates lying in the target of the normal-form chart, close to the coordinate `z₀` of the base
point. -/
def chartW1 (w : S.Pre) : Set (EuclideanSpace ℝ (Fin ((8 + k) + 1))) :=
  (𝓡∂ ((8 + k) + 1)).symm ⁻¹' (S.domChartAt w).target
    ∩ Metric.ball (chartZ S w) (chartRho S w)

theorem chartW1_open (w : S.Pre) : IsOpen (chartW1 S w) :=
  ((S.domChartAt w).open_target.preimage (𝓡∂ ((8 + k) + 1)).continuous_symm).inter
    Metric.isOpen_ball

theorem chartZ_mem_chartW1 (w : S.Pre) : chartZ S w ∈ chartW1 S w := by
  refine ⟨?_, Metric.mem_ball_self (chartRho_pos S w)⟩
  show (𝓡∂ ((8 + k) + 1)).symm
    ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) w.1) ∈ (S.domChartAt w).target
  rw [show (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) w.1
      = (𝓡∂ ((8 + k) + 1)) ((S.domChartAt w) w.1) from rfl,
    (𝓡∂ ((8 + k) + 1)).left_inv]
  exact (S.domChartAt w).map_source (mem_domChartAt_source S w)
noncomputable def chartHmap (w : S.Pre) :
    EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
  fun y => chartZ S w + chartIota S w (y - chartEps S w • Work.Surgery.e₀ 8)

theorem chartHmap_apply (w : S.Pre) (y : EuclideanSpace ℝ (Fin 9)) :
    chartHmap S w y = chartZ S w + chartIota S w (y - chartEps S w • Work.Surgery.e₀ 8) := rfl

theorem chartHmap_sub (w : S.Pre) (y : EuclideanSpace ℝ (Fin 9)) :
    chartHmap S w y - chartZ S w = chartIota S w (y - chartEps S w • Work.Surgery.e₀ 8) := by
  rw [chartHmap_apply, add_sub_cancel_left]

theorem chartHmap_coord_boundary (w : S.Pre)
    (h : w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M) (y : EuclideanSpace ℝ (Fin 9)) :
    (chartHmap S w y) 0 = y 0 := by
  rw [chartHmap_apply, chartEps_eq_zero S w h, zero_smul, sub_zero, PiLp.add_apply,
    chartZ_coord_eq_zero S w h, chartIota_coord S w h, zero_add]

theorem chartHmap_coord_pos (w : S.Pre)
    (h : w.1 ∉ (𝓡∂ ((8 + k) + 1)).boundary S.M) {y : EuclideanSpace ℝ (Fin 9)}
    (hy : chartHmap S w y ∈ Metric.ball (chartZ S w) (chartRho S w)) :
    0 < (chartHmap S w y) 0 := by
  have hball : ‖chartHmap S w y - chartZ S w‖ < chartRho S w := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hy
  have happ : |(chartHmap S w y - chartZ S w) 0| ≤ ‖chartHmap S w y - chartZ S w‖ := by
    simpa using PiLp.norm_apply_le (chartHmap S w y - chartZ S w) (0 : Fin ((8 + k) + 1))
  have hsub : (chartHmap S w y) 0 = (chartHmap S w y - chartZ S w) 0 + (chartZ S w) 0 := by
    rw [PiLp.sub_apply]; ring
  have hz := chartZ_coord_pos S w h
  have hle := chartRho_le_coord S w h
  rw [hsub]
  have := (abs_le.mp happ).1
  linarith

/-- The inverse chart value (as a point of `M`). -/
noncomputable def chartInvVal (w : S.Pre) (y : EuclideanHalfSpace 9) : S.M :=
  ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1))).symm (chartHmap S w y.1)

/-- The source of the chart: the points of `W` whose normal-form coordinates lie in `chartW1`,
together with the condition that the underlying point of `M` lies in `U w`. -/
def chartSource (w : S.Pre) : Set S.Pre :=
  {z | z.1 ∈ (S.domChartAt w).source
    ∧ (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 ∈ chartW1 S w
    ∧ z.1 ∈ S.data.U w}

theorem chartSource_open (w : S.Pre) : IsOpen (chartSource S w) := by
  have hcont : ContinuousOn
      (fun z : S.Pre => (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1)
      {z : S.Pre | z.1 ∈ (S.domChartAt w).source} :=
    (OpenPartialHomeomorph.continuousOn_extend (S.domChartAt w)).comp
      continuous_subtype_val.continuousOn
      (fun z hz => by simpa [OpenPartialHomeomorph.extend_source] using hz)
  have hset : chartSource S w
      = ({z : S.Pre | z.1 ∈ (S.domChartAt w).source} ∩
          ((fun z : S.Pre => (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1) ⁻¹'
            chartW1 S w)) ∩ Subtype.val ⁻¹' S.data.U w := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
  rw [hset]
  exact (hcont.isOpen_inter_preimage
    ((S.domChartAt w).open_source.preimage continuous_subtype_val) (chartW1_open S w)).inter
    ((S.data.isOpen_U w).preimage continuous_subtype_val)

theorem aLin_extend_eq (w : S.Pre) {z : S.Pre} (hz : z ∈ chartSource S w) :
    aLin S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1) = aLin S w (chartZ S w) := by
  have h := equivAt_fst_eq_of_mem_core S w hz.1 hz.2.2 z.2
  rw [chartZ, aLin_apply, aLin_apply]
  exact h

theorem aLin_chartZ_sub (w : S.Pre) {z : S.Pre} (hz : z ∈ chartSource S w) :
    aLin S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w) = 0 := by
  rw [map_sub, sub_eq_zero]
  exact aLin_extend_eq S w hz

theorem chartHmap_mem_extend_target (w : S.Pre) {y : EuclideanHalfSpace 9}
    (hy : chartHmap S w y.1 ∈ chartW1 S w) :
    chartHmap S w y.1 ∈ ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1))).target := by
  rw [OpenPartialHomeomorph.extend_target]
  refine ⟨hy.1, ?_⟩
  rw [Work.Surgery.range_halfModel]
  rcases Classical.em (w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M) with h | h
  · show 0 ≤ (chartHmap S w y.1) 0
    rw [chartHmap_coord_boundary S w h y.1]
    exact y.2
  · exact le_of_lt (chartHmap_coord_pos S w h hy.2)

/-- The target of the chart. -/
def chartTarget (w : S.Pre) : Set (EuclideanHalfSpace 9) :=
  {y | chartHmap S w y.1 ∈ chartW1 S w ∧ chartInvVal S w y ∈ S.data.U w}

theorem chartTarget_open (w : S.Pre) : IsOpen (chartTarget S w) := by
  have hcont : Continuous (fun y : EuclideanHalfSpace 9 =>
      chartHmap S w y.1) :=
    continuous_const.add ((chartIota S w).continuous.comp
      (continuous_subtype_val.sub continuous_const))
  have hcont2 : ContinuousOn (fun y : EuclideanHalfSpace 9 => chartInvVal S w y)
      {y : EuclideanHalfSpace 9 | chartHmap S w y.1 ∈ chartW1 S w} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous (fun y : ↥{y : EuclideanHalfSpace 9 |
        chartHmap S w y.1 ∈ chartW1 S w} => chartHmap S w y.1.1) :=
      hcont.comp continuous_subtype_val
    exact (OpenPartialHomeomorph.continuousOn_extend_symm (S.domChartAt w)).comp_continuous
      h1 (fun y => chartHmap_mem_extend_target S w y.2)
  have hset : chartTarget S w
      = ({y : EuclideanHalfSpace 9 | chartHmap S w y.1 ∈ chartW1 S w} ∩
          (fun y : EuclideanHalfSpace 9 => chartInvVal S w y) ⁻¹' S.data.U w) := by
    ext y
    exact Iff.rfl
  rw [hset]
  exact hcont2.isOpen_inter_preimage ((chartW1_open S w).preimage hcont)
    (S.data.isOpen_U w)

theorem chartInvVal_spec (w : S.Pre) {y : EuclideanHalfSpace 9} (hy : y ∈ chartTarget S w) :
    (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) (chartInvVal S w y) = chartHmap S w y.1 :=
  PartialEquiv.right_inv _ (chartHmap_mem_extend_target S w hy.1)

theorem chartInvVal_mem_source (w : S.Pre) {y : EuclideanHalfSpace 9}
    (hy : y ∈ chartTarget S w) : chartInvVal S w y ∈ (S.domChartAt w).source := by
  have h := PartialEquiv.map_target ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)))
    (chartHmap_mem_extend_target S w hy.1)
  simpa [chartInvVal, OpenPartialHomeomorph.extend_source] using h
noncomputable def chartFun (w : S.Pre) (z : S.Pre) : EuclideanSpace ℝ (Fin 9) :=
  chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w)
    + chartEps S w • Work.Surgery.e₀ 8

theorem chartHmap_chartFun (w : S.Pre) {z : S.Pre} (hz : z ∈ chartSource S w) :
    chartHmap S w (chartFun S w z) = (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 := by
  have h1 : chartFun S w z - chartEps S w • Work.Surgery.e₀ 8
      = chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w) := by
    have h2 : chartFun S w z = chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1
        - chartZ S w) + chartEps S w • Work.Surgery.e₀ 8 := rfl
    rw [h2, add_sub_cancel_right]
  have h3 : chartIota S w (chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1
      - chartZ S w)) = (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w :=
    chartIota_beta S w (aLin_chartZ_sub S w hz)
  rw [chartHmap_apply, h1, h3]
  exact add_sub_cancel _ _

theorem chartFun_coord_nonneg (w : S.Pre) {z : S.Pre} (hz : z ∈ chartSource S w) :
    0 ≤ (chartFun S w z) 0 := by
  have hv : (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w
      = (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w := rfl
  rcases Classical.em (w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M) with h | h
  · rw [chartFun, PiLp.add_apply, chartEps_eq_zero S w h, zero_smul, PiLp.zero_apply, add_zero,
      chartBeta_apply]
    rw [chartT_snd_coord S w h _ (aLin_chartZ_sub S w hz), sLin_apply, PiLp.sub_apply,
      chartZ_coord_eq_zero S w h, sub_zero]
    exact zero_le_extend_apply_coord (m := (8 + k) + 1) (S.domChartAt w) hz.1
  · have hball : ‖(S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w‖
        < chartRho S w := by
      have hmem : (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1
          ∈ Metric.ball (chartZ S w) (chartRho S w) := hz.2.1.2
      rwa [Metric.mem_ball, dist_eq_norm] at hmem
    have hcoord : -‖chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w)‖
        ≤ (chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w)) 0 := by
      have h1 : |(chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1
          - chartZ S w)) 0|
          ≤ ‖chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w)‖ := by
        simpa using PiLp.norm_apply_le
          (chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w))
          (0 : Fin 9)
      linarith [(abs_le.mp h1).1]
    have hbound : ‖chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w)‖
        ≤ ‖chartBeta S w‖ * chartRho S w := by
      calc ‖chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w)‖
          ≤ ‖chartBeta S w‖ * ‖(S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1 - chartZ S w‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖chartBeta S w‖ * chartRho S w :=
            mul_le_mul_of_nonneg_left hball.le (norm_nonneg _)
    rw [chartFun, PiLp.add_apply, PiLp.smul_apply, Work.Surgery.e₀_apply_zero, smul_eq_mul,
      mul_one, chartEps, dif_neg h]
    nlinarith [hcoord, hbound]

theorem chartFun_mem_chartTarget (w : S.Pre) {z : S.Pre} (hz : z ∈ chartSource S w) :
    (⟨chartFun S w z, chartFun_coord_nonneg S w hz⟩ : EuclideanHalfSpace 9) ∈ chartTarget S w := by
  refine ⟨?_, ?_⟩
  · show chartHmap S w (chartFun S w z) ∈ chartW1 S w
    rw [chartHmap_chartFun S w hz]
    exact hz.2.1
  · show chartInvVal S w (⟨chartFun S w z, chartFun_coord_nonneg S w hz⟩ : EuclideanHalfSpace 9)
      ∈ S.data.U w
    rw [chartInvVal, chartHmap_chartFun S w hz]
    rw [PartialEquiv.left_inv _ (by simpa [OpenPartialHomeomorph.extend_source] using hz.1)]
    exact hz.2.2

theorem aLin_chartHmap (w : S.Pre) (y : EuclideanHalfSpace 9) :
    aLin S w (chartHmap S w y.1) = aLin S w (chartZ S w) := by
  rw [chartHmap_apply, map_add, chartIota_mem_ker, add_zero]

theorem chartInvVal_mem_W (w : S.Pre) {y : EuclideanHalfSpace 9}
    (hy : y ∈ chartTarget S w) : chartInvVal S w y ∈ S.W := by
  have hsrc := chartInvVal_mem_source S w hy
  have hspec := chartInvVal_spec S w hy
  have hmem1 : S.localMap w (chartInvVal S w y) ∈ (S.codChartAt w).source :=
    domChartAt_source_subset S w hsrc
  have hmem2 : S.localMap w w.1 ∈ (S.codChartAt w).source :=
    domChartAt_source_subset S w (mem_domChartAt_source S w)
  have h1 : S.codChartAt w (S.localMap w (chartInvVal S w y))
      = S.codChartAt w (S.localMap w w.1) := by
    have hL : (S.equivAt w (chartHmap S w y.1)).1 = aLin S w (chartZ S w) := by
      rw [← aLin_apply]
      exact aLin_chartHmap S w y
    rw [codChartAt_localMap S w hsrc, hspec, hL]
    show aLin S w (chartZ S w) = S.codChartAt w (S.localMap w w.1)
    rw [chartZ, codChartAt_localMap S w (mem_domChartAt_source S w)]
    exact (aLin_apply S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) w.1)).symm
  have h2 : S.localMap w (chartInvVal S w y) = S.localMap w w.1 :=
    calc S.localMap w (chartInvVal S w y)
        = (S.codChartAt w).symm (S.codChartAt w (S.localMap w (chartInvVal S w y))) :=
          (PartialEquiv.left_inv _ hmem1).symm
      _ = (S.codChartAt w).symm (S.codChartAt w (S.localMap w w.1)) := by rw [h1]
      _ = S.localMap w w.1 := PartialEquiv.left_inv _ hmem2
  have h3 : S.localMap w (chartInvVal S w y) = 0 := by
    rw [h2]
    exact S.localMap_self w
  exact (S.localMap_eq_zero_iff w hy.2).mp h3

theorem chartInvVal_mem_chartSource (w : S.Pre) {y : EuclideanHalfSpace 9}
    (hy : y ∈ chartTarget S w) :
    (⟨chartInvVal S w y, chartInvVal_mem_W S w hy⟩ : S.Pre) ∈ chartSource S w := by
  refine ⟨chartInvVal_mem_source S w hy, ?_, hy.2⟩
  rw [chartInvVal_spec S w hy]
  exact hy.1

noncomputable def chartInvFun (w : S.Pre) (y : EuclideanHalfSpace 9) : S.Pre :=
  if hy : y ∈ chartTarget S w then ⟨chartInvVal S w y, chartInvVal_mem_W S w hy⟩ else w

theorem chartInvFun_of_mem (w : S.Pre) {y : EuclideanHalfSpace 9}
    (hy : y ∈ chartTarget S w) :
    chartInvFun S w y = ⟨chartInvVal S w y, chartInvVal_mem_W S w hy⟩ :=
  dif_pos hy

theorem chartInvFun_mem_source (w : S.Pre) {y : EuclideanHalfSpace 9}
    (hy : y ∈ chartTarget S w) : chartInvFun S w y ∈ chartSource S w := by
  rw [chartInvFun_of_mem S w hy]
  exact chartInvVal_mem_chartSource S w hy

theorem chartInvVal_chartFun (w : S.Pre) {z : S.Pre} (hz : z ∈ chartSource S w) :
    chartInvVal S w ⟨chartFun S w z, chartFun_coord_nonneg S w hz⟩ = z.1 := by
  rw [chartInvVal, chartHmap_chartFun S w hz]
  exact PartialEquiv.left_inv _
    (by simpa [OpenPartialHomeomorph.extend_source] using hz.1)

theorem chartFun_invFun (w : S.Pre) {y : EuclideanHalfSpace 9}
    (hy : y ∈ chartTarget S w) :
    chartFun S w (chartInvFun S w y) = y.1 := by
  have hval : (chartInvFun S w y).1 = chartInvVal S w y := by
    rw [chartInvFun_of_mem S w hy]
  rw [chartFun, hval, chartInvVal_spec S w hy, chartHmap_sub, chartBeta_iota]
  exact sub_add_cancel _ _

/-- The chart of the transverse preimage at `w`, into the half-space of dimension `9`. -/
noncomputable def chartAt (w : S.Pre) : OpenPartialHomeomorph S.Pre (EuclideanHalfSpace 9) where
  toFun z := if hz : z ∈ chartSource S w then
      ⟨chartFun S w z, chartFun_coord_nonneg S w hz⟩
    else ⟨0, by simp⟩
  invFun y := chartInvFun S w y
  source := chartSource S w
  target := chartTarget S w
  map_source' z hz := by
    rw [dif_pos hz]
    exact chartFun_mem_chartTarget S w hz
  map_target' y hy := chartInvFun_mem_source S w hy
  left_inv' z hz := by
    rw [dif_pos hz]
    have hmem : (⟨chartFun S w z, chartFun_coord_nonneg S w hz⟩ : EuclideanHalfSpace 9)
        ∈ chartTarget S w := chartFun_mem_chartTarget S w hz
    rw [chartInvFun_of_mem S w hmem]
    exact Subtype.ext (chartInvVal_chartFun S w hz)
  right_inv' y hy := by
    have hmem : (⟨chartInvVal S w y, chartInvVal_mem_W S w hy⟩ : S.Pre) ∈ chartSource S w :=
      chartInvVal_mem_chartSource S w hy
    rw [chartInvFun_of_mem S w hy, dif_pos hmem]
    refine Subtype.ext ?_
    show chartFun S w ⟨chartInvVal S w y, chartInvVal_mem_W S w hy⟩ = y.1
    rw [chartFun, chartInvVal_spec S w hy, chartHmap_sub, chartBeta_iota]
    exact sub_add_cancel _ _
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous (fun z : ↥(chartSource S w) =>
        (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) z.1.1) :=
      (OpenPartialHomeomorph.continuousOn_extend (S.domChartAt w)).comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val)
        (fun z => by simpa [OpenPartialHomeomorph.extend_source] using z.2.1)
    have h2 : Continuous (fun z : ↥(chartSource S w) => chartFun S w z.1) := by
      simp only [chartFun]
      exact ((chartBeta S w).continuous.comp (h1.sub continuous_const)).add continuous_const
    have haux : (chartSource S w).domRestrict (fun z : S.Pre =>
        if hz : z ∈ chartSource S w then ⟨chartFun S w z, chartFun_coord_nonneg S w hz⟩
        else (⟨0, by simp⟩ : EuclideanHalfSpace 9))
        = fun z : ↥(chartSource S w) => ⟨chartFun S w z.1, chartFun_coord_nonneg S w z.2⟩ := by
      funext z
      rw [Set.domRestrict_apply, dif_pos z.2]
    rw [haux]
    exact Continuous.subtype_mk h2 (fun z => chartFun_coord_nonneg S w z.2)
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous (fun y : ↥(chartTarget S w) => chartHmap S w y.1.1) := by
      have hsub : Continuous (fun y : ↥(chartTarget S w) =>
          (y.1.1 : EuclideanSpace ℝ (Fin 9)) - chartEps S w • Work.Surgery.e₀ 8) :=
        (continuous_subtype_val.comp continuous_subtype_val).sub continuous_const
      exact continuous_const.add ((chartIota S w).continuous.comp hsub)
    have haux : (chartTarget S w).domRestrict (chartInvFun S w)
        = fun y : ↥(chartTarget S w) =>
          (⟨chartInvVal S w y.1, chartInvVal_mem_W S w y.2⟩ : S.Pre) := by
      funext y
      rw [Set.domRestrict_apply, chartInvFun_of_mem S w y.2]
    rw [haux]
    refine Continuous.subtype_mk
      (f := fun y : ↥(chartTarget S w) => chartInvVal S w y.1) ?_
      (fun y : ↥(chartTarget S w) => chartInvVal_mem_W S w y.2)
    exact (OpenPartialHomeomorph.continuousOn_extend_symm (S.domChartAt w)).comp_continuous
      h1 (fun y : ↥(chartTarget S w) => chartHmap_mem_extend_target S w y.2.1)
  open_source := chartSource_open S w
  open_target := chartTarget_open S w


end Setup

end Lvl

end

end Work.PTGeometric
