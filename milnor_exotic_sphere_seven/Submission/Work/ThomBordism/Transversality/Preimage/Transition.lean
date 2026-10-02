import Submission.Work.ThomBordism.Transversality.Preimage.Chart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Smoothness of the transitions between the charts of the transverse preimage

For two points `w w'` of the transverse preimage `S.Pre = F ⁻¹' X.core`, the transition between the
charts `chartAt S w` and `chartAt S w'` is, on the level of the model space, the ambient change of
charts `extendCoordChange (domChartAt w) (domChartAt w')` conjugated by the two affine normal forms.
The key computation is `transAux_eq_chartAt_trans`.
-/

open scoped Manifold Topology ContDiff
open Function Set Manifold
open ModelWithCorners
open Classical

namespace Work.ThomBordism.Transversality.Preimage

noncomputable section

namespace CoreSetup

variable {k : ℕ} (S : CoreSetup k)

/-- The model-level form of the transition between the charts at `w` and `w'`: the transition
between the two ambient normal-form charts, followed by the linear map `chartBeta S w'`. -/
noncomputable def transAux (w w' : S.Pre) (y : EuclideanSpace ℝ (Fin 9)) :
    EuclideanSpace ℝ (Fin 9) :=
  chartBeta S w' ((S.domChartAt w').extend (𝓡∂ ((8 + k) + 1))
      (((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1))).symm (chartHmap S w y)))
    - chartBeta S w' (chartZ S w') + chartEps S w' • Work.Surgery.e₀ 8

theorem contDiffOn_transAux (w w' : S.Pre) :
    ContDiffOn ℝ smoothHeight (transAux S w w')
      {y : EuclideanSpace ℝ (Fin 9) | chartHmap S w y ∈
        ((𝓡∂ ((8 + k) + 1)).extendCoordChange (S.domChartAt w) (S.domChartAt w')).source} := by
  have h1 : ContDiffOn ℝ smoothHeight (fun y : EuclideanSpace ℝ (Fin 9) => chartHmap S w y)
      univ := by
    have hch : (fun y : EuclideanSpace ℝ (Fin 9) => chartHmap S w y)
        = fun y : EuclideanSpace ℝ (Fin 9) =>
            chartZ S w + chartIota S w (y - chartEps S w • Work.Surgery.e₀ 8) :=
      funext fun y => chartHmap_apply S w y
    rw [hch]
    exact contDiffOn_const.add (((chartIota S w).contDiff.fun_comp_contDiffOn
      (contDiffOn_id.sub contDiffOn_const)))
  have h2 : ContDiffOn ℝ smoothHeight
      (fun z : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
        ((𝓡∂ ((8 + k) + 1)).extendCoordChange (S.domChartAt w) (S.domChartAt w')) z)
      ((𝓡∂ ((8 + k) + 1)).extendCoordChange (S.domChartAt w) (S.domChartAt w')).source :=
    contDiffOn_extendCoordChange (I := 𝓡∂ ((8 + k) + 1))
      (domChartAt_mem_maximalAtlas S w) (domChartAt_mem_maximalAtlas S w')
  have h3 : ContDiffOn ℝ smoothHeight
      (fun y : EuclideanSpace ℝ (Fin 9) =>
        ((𝓡∂ ((8 + k) + 1)).extendCoordChange (S.domChartAt w) (S.domChartAt w'))
          (chartHmap S w y))
      {y : EuclideanSpace ℝ (Fin 9) | chartHmap S w y ∈
        ((𝓡∂ ((8 + k) + 1)).extendCoordChange (S.domChartAt w) (S.domChartAt w')).source} :=
    h2.comp (h1.mono (Set.subset_univ _)) (fun y hy => hy)
  have h4 : ContDiffOn ℝ smoothHeight
      (fun y : EuclideanSpace ℝ (Fin 9) =>
        (chartBeta S w') (((𝓡∂ ((8 + k) + 1)).extendCoordChange
          (S.domChartAt w) (S.domChartAt w')) (chartHmap S w y)))
      {y : EuclideanSpace ℝ (Fin 9) | chartHmap S w y ∈
        ((𝓡∂ ((8 + k) + 1)).extendCoordChange (S.domChartAt w) (S.domChartAt w')).source} :=
    (chartBeta S w').contDiff.fun_comp_contDiffOn h3
  exact (h4.sub contDiffOn_const).add contDiffOn_const

theorem range_mem_coord {y : EuclideanSpace ℝ (Fin 9)} (hy : y ∈ range (𝓡∂ 9)) : 0 ≤ y 0 := by
  rw [Work.Surgery.range_halfModel] at hy
  exact hy

theorem symm_val_of_mem_range {y : EuclideanSpace ℝ (Fin 9)} (hy : y ∈ range (𝓡∂ 9)) :
    ((𝓡∂ 9).symm y).1 = y := by
  rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (range_mem_coord hy)]

theorem chartAt_apply_of_mem (w : S.Pre) {z : S.Pre} (hz : z ∈ chartSource S w) :
    chartAt S w z = ⟨chartFun S w z, chartFun_coord_nonneg S w hz⟩ := by
  rw [chartAt]
  exact dif_pos hz

theorem chartAt_symm_apply (w : S.Pre) (y : EuclideanHalfSpace 9) :
    (chartAt S w).symm y = chartInvFun S w y := rfl

theorem chartAt_trans_apply (w w' : S.Pre) (y : EuclideanHalfSpace 9) :
    (OpenPartialHomeomorph.trans (chartAt S w).symm (chartAt S w')) y
      = chartAt S w' (chartInvFun S w y) := by
  rw [OpenPartialHomeomorph.trans_apply, chartAt_symm_apply S w]

/-- **The transition between the charts is the ambient change of charts in the normal-form
coordinates.** -/
theorem transAux_eq_chartAt_trans (w w' : S.Pre) {y : EuclideanSpace ℝ (Fin 9)}
    (hy : y ∈ range (𝓡∂ 9)) (hct : (𝓡∂ 9).symm y ∈ chartTarget S w)
    (hcs : chartInvFun S w ((𝓡∂ 9).symm y) ∈ chartSource S w') :
    transAux S w w' y = (𝓡∂ 9)
      ((OpenPartialHomeomorph.trans (chartAt S w).symm (chartAt S w')) ((𝓡∂ 9).symm y)) := by
  have hT : (OpenPartialHomeomorph.trans (chartAt S w).symm (chartAt S w')) ((𝓡∂ 9).symm y)
      = ⟨chartFun S w' (chartInvFun S w ((𝓡∂ 9).symm y)),
          chartFun_coord_nonneg S w' hcs⟩ := by
    rw [chartAt_trans_apply S w w']
    exact chartAt_apply_of_mem S w' hcs
  have hval : (chartInvFun S w ((𝓡∂ 9).symm y)).1 = chartInvVal S w ((𝓡∂ 9).symm y) := by
    rw [chartInvFun_of_mem S w hct]
  have harg : (S.domChartAt w').extend (𝓡∂ ((8 + k) + 1))
        (((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1))).symm (chartHmap S w y))
      = (S.domChartAt w').extend (𝓡∂ ((8 + k) + 1))
        (chartInvFun S w ((𝓡∂ 9).symm y)).1 := by
    rw [hval, chartInvVal, symm_val_of_mem_range hy]
  rw [hT, modelWithCornersEuclideanHalfSpace_apply]
  show transAux S w w' y = chartBeta S w' ((S.domChartAt w').extend (𝓡∂ ((8 + k) + 1))
      (chartInvFun S w ((𝓡∂ 9).symm y)).1 - chartZ S w')
      + chartEps S w' • Work.Surgery.e₀ 8
  rw [transAux, harg, ContinuousLinearMap.map_sub]

theorem contDiffOn_chartAt_trans (w w' : S.Pre) :
    ContDiffOn ℝ smoothHeight
      (fun y : EuclideanSpace ℝ (Fin 9) =>
        (𝓡∂ 9) ((OpenPartialHomeomorph.trans (chartAt S w).symm (chartAt S w'))
          ((𝓡∂ 9).symm y)))
      ((𝓡∂ 9).symm ⁻¹' (OpenPartialHomeomorph.trans (chartAt S w).symm (chartAt S w')).source
        ∩ range (𝓡∂ 9)) := by
  set Sset : Set (EuclideanSpace ℝ (Fin 9)) :=
    (𝓡∂ 9).symm ⁻¹' (OpenPartialHomeomorph.trans (chartAt S w).symm (chartAt S w')).source
      ∩ range (𝓡∂ 9) with hSset
  have hct_of : ∀ y ∈ Sset, (𝓡∂ 9).symm y ∈ chartTarget S w := by
    intro y hy
    have h := hy.1
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
    exact h.1
  have hcs_of : ∀ y ∈ Sset, chartInvFun S w ((𝓡∂ 9).symm y) ∈ chartSource S w' := by
    intro y hy
    have h := hy.1
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
    exact h.2
  have hsub : Sset ⊆ {y : EuclideanSpace ℝ (Fin 9) | chartHmap S w y ∈
      ((𝓡∂ ((8 + k) + 1)).extendCoordChange (S.domChartAt w) (S.domChartAt w')).source} := by
    intro y hy
    have hct := hct_of y hy
    have hcs := hcs_of y hy
    have hsource : (chartInvFun S w ((𝓡∂ 9).symm y)).1 ∈ (S.domChartAt w).source := by
      rw [chartInvFun_of_mem S w hct]
      exact chartInvVal_mem_source S w hct
    have hsource' : (chartInvFun S w ((𝓡∂ 9).symm y)).1 ∈ (S.domChartAt w').source := hcs.1
    rw [show ((𝓡∂ ((8 + k) + 1)).extendCoordChange (S.domChartAt w) (S.domChartAt w')).source
        = (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) ''
            ((S.domChartAt w).source ∩ (S.domChartAt w').source)
        from (OpenPartialHomeomorph.extend_image_source_inter
          (I := 𝓡∂ ((8 + k) + 1)) (S.domChartAt w) (S.domChartAt w')).symm]
    refine ⟨(chartInvFun S w ((𝓡∂ 9).symm y)).1, ⟨hsource, hsource'⟩, ?_⟩
    rw [chartInvFun_of_mem S w hct, chartInvVal_spec S w hct, symm_val_of_mem_range hy.2]
  have heq : ∀ y ∈ Sset, transAux S w w' y =
      (𝓡∂ 9) ((OpenPartialHomeomorph.trans (chartAt S w).symm (chartAt S w'))
        ((𝓡∂ 9).symm y)) :=
    fun y hy => transAux_eq_chartAt_trans S w w' hy.2 (hct_of y hy) (hcs_of y hy)
  exact ((contDiffOn_transAux S w w').mono hsub).congr (fun y hy => (heq y hy).symm)

end CoreSetup

end

end Work.ThomBordism.Transversality.Preimage
