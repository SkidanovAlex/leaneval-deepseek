import Mathlib
import Submission.Work.ThomBordism.FrameSigns.Charts
import Submission.Work.ThomBordism.FrameSigns.frameSign_eq_of_isCoordBall
import Submission.Work.ThomBordism.FrameSigns.chartCoh_compare
import Submission.Work.ThomBordism.FrameSigns.chartCoh_pair_ne_zero
import Submission.Work.ThomBordism.FrameSigns.chartTrans_germ
import Submission.Work.Orient.Closed

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The assembly of the tangent frame signs

From
* `Work.ThomBordism.FrameSigns.frameSign_eq_of_isCoordBall` (local constancy of the chart frame sign
  on a coordinate ball),
* `Work.ThomBordism.FrameSigns.chartCoh_compare` and
  `Work.ThomBordism.FrameSigns.chartCoh_pair_ne_zero` (the comparison of the chart classes at a
  common point and the non-vanishing of their Kronecker pairings), and
* `Work.ThomBordism.FrameSigns.chartTrans_germ` (invertibility of the transition derivative),

this file assembles the target: for a closed smooth `8`-manifold `V` there are signs
`frameSign V i x ∈ {±1}`, continuous on the chart sources, whose product on an overlap is the sign of
the transition Jacobian.
-/

open Classical CategoryTheory Filter

namespace Work.ThomBordism.FrameSigns

noncomputable section

/-! ## A coordinate ball inside a prescribed open set -/

/-- **A coordinate ball inside a prescribed open neighbourhood of a point.** -/
theorem exists_isCoordBall_subset (V : Man8) (U : Set V.pt) (hU : IsOpen U) {x : V.pt}
    (hx : x ∈ U) :
    ∃ K : Set V.pt, IsCoordBall 8 (TopCat.of V.pt) K ∧ x ∈ K ∧ K ∈ nhds x ∧ K ⊆ U := by
  set e := chartAt (EuclideanSpace ℝ (Fin 8)) x with he
  have hxe : x ∈ e.source := mem_chart_source _ x
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxe)
  have hcont : ContinuousAt (fun w => e.symm w) (e x) := e.continuousAt_symm (e.map_source hxe)
  have hmem : e.symm ⁻¹' U ∈ nhds (e x) :=
    hcont.preimage_mem_nhds (hU.mem_nhds (by rw [e.left_inv hxe]; exact hx))
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨e ⁻¹' Metric.closedBall (e x) (min r₁ r₂ / 2) ∩ e.source, ?_, ?_, ?_, ?_⟩
  · refine ⟨x, min r₁ r₂, lt_min hr₁ hr₂, ?_, rfl⟩
    exact fun y hy => h₁ (Metric.ball_subset_ball (min_le_left r₁ r₂) hy)
  · refine ⟨?_, hxe⟩
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_self]
    have := lt_min hr₁ hr₂
    linarith
  · have hopen : IsOpen (e ⁻¹' Metric.ball (e x) (min r₁ r₂ / 2) ∩ e.source) := by
      rw [Set.inter_comm]
      exact e.isOpen_inter_preimage Metric.isOpen_ball
    have hmem' : x ∈ e ⁻¹' Metric.ball (e x) (min r₁ r₂ / 2) ∩ e.source := by
      refine ⟨?_, hxe⟩
      rw [Set.mem_preimage, Metric.mem_ball, dist_self]
      have := lt_min hr₁ hr₂
      linarith
    refine Filter.mem_of_superset (hopen.mem_nhds hmem') ?_
    intro z hz
    exact Set.mem_inter (Metric.ball_subset_closedBall hz.1) hz.2
  · intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hle1 : min r₁ r₂ / 2 ≤ r₁ := by have := min_le_left r₁ r₂; linarith
    have hle2 : min r₁ r₂ / 2 ≤ r₂ := by have := min_le_right r₁ r₂; linarith
    have hd : dist (e z) (e x) ≤ min r₁ r₂ / 2 := Metric.mem_closedBall.mp hz1
    have hd2 : dist (e z) (e x) < r₂ := by
      have := min_le_right r₁ r₂
      linarith
    have hmem_ball : e z ∈ Metric.ball (e x) r₂ :=
      Metric.mem_ball.mpr (by simpa [dist_comm] using hd2)
    have hUz : e.symm (e z) ∈ U := h₂ hmem_ball
    rwa [e.left_inv hz2] at hUz

/-! ## Continuity of the chart frame sign -/

/-- **The chart frame sign is continuous on the chart source.** -/
theorem continuousOn_frameSign (V : Man8) (i : ChartIdx V) :
    ContinuousOn (frameSign V i) (src V i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine IsLocallyConstant.continuous ?_
  intro s
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨K, hK, hxK, hKn, hKU⟩ :=
    exists_isCoordBall_subset V (src V i) (chartOf V i).1.open_source x.2
  obtain ⟨W, hWK, hWopen, hxW⟩ := mem_nhds_iff.mp hKn
  refine Filter.mem_of_superset
    ((continuous_subtype_val.isOpen_preimage W hWopen).mem_nhds hxW) ?_
  intro y hy
  show frameSign V i y ∈ s
  rw [frameSign_eq_of_isCoordBall V i hK hKU (hWK hy) (hWK hxW)]
  exact hx

/-! ## The product relation -/

/-- The determinant of the transition derivative is nonzero (it is the derivative of a germ
diffeomorphism). -/
theorem transDet_ne_zero (V : Man8) (i j : ChartIdx V) {x : V.pt} (hi : x ∈ src V i)
    (hj : x ∈ src V j) :
    LinearMap.det (ContinuousLinearMap.toLinearMap
      (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x))) ≠ 0 := by
  obtain ⟨-, -, -, -, -, hbij⟩ := chartTrans_germ V i j hi hj
  set L : EuclideanSpace ℝ (Fin 8) →ₗ[ℝ] EuclideanSpace ℝ (Fin 8) :=
    (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y))
      ((chartOf V i).1 x)).toLinearMap with hL
  have hbij' : Function.Bijective L := hbij
  have h1 : IsUnit L := (Module.End.isUnit_iff L).mpr hbij'
  have h2 : IsUnit (LinearMap.det L) := (LinearMap.isUnit_iff_isUnit_det L).mp h1
  exact h2.ne_zero

/-- **The third conjunct**: the product of the two chart frame signs at a common point is the sign of
the transition Jacobian. -/
theorem frameSign_mul (V : Man8) (i j : ChartIdx V) {x : V.pt} (hi : x ∈ src V i)
    (hj : x ∈ src V j) :
    frameSign V i x * frameSign V j x
      = Real.sign (LinearMap.det (ContinuousLinearMap.toLinearMap
        (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)))) := by
  set D : ℝ := LinearMap.det (ContinuousLinearMap.toLinearMap
    (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x))) with hD
  have hDne : D ≠ 0 := by
    rw [hD]
    exact transDet_ne_zero V i j hi hj
  set ni := pairVal V i x hi with hni
  set nj := pairVal V j x hj with hnj
  have hni_ne : ni ≠ 0 := by rw [hni]; exact chartCoh_pair_ne_zero V i hi
  have hnj_ne : nj ≠ 0 := by rw [hnj]; exact chartCoh_pair_ne_zero V j hj
  have hrel : ni = (if 0 < D then (1 : ℤ) else -1) * nj := by
    have hcmp := chartCoh_compare V i j hi hj
    rw [hni, hnj]
    simp only [pairVal]
    rw [hcmp, map_zsmul]
    split_ifs
    · rfl
    · rw [LinearMap.smul_apply, Int.zsmul_eq_mul]
  have hfi : frameSign V i x = (if 0 < ni then (1 : ℝ) else -1) := by
    rw [frameSign_of_mem V i x hi, ← hni]
  have hfj : frameSign V j x = (if 0 < nj then (1 : ℝ) else -1) := by
    rw [frameSign_of_mem V j x hj, ← hnj]
  have hsign : Real.sign D = (if 0 < D then (1 : ℝ) else -1) := by
    rcases lt_or_gt_of_ne hDne with h | h
    · rw [Real.sign_of_neg h, if_neg (not_lt.mpr h.le)]
    · rw [Real.sign_of_pos h, if_pos h]
  rw [hfi, hfj, hsign]
  by_cases hDc : (0 : ℝ) < D
  · have heps : (if 0 < D then (1 : ℤ) else -1) = 1 := if_pos hDc
    have hiff : (0 < ni) ↔ (0 < nj) := by
      rw [hrel, heps, one_mul]
    rw [if_pos hDc]
    by_cases hj' : (0 : ℤ) < nj
    · rw [if_pos (hiff.mpr hj'), if_pos hj']
      norm_num
    · rw [if_neg (fun h => hj' (hiff.mp h)), if_neg hj']
      norm_num
  · have heps : (if 0 < D then (1 : ℤ) else -1) = -1 := if_neg hDc
    have hiff : (0 < ni) ↔ (nj < 0) := by
      rw [hrel, heps]
      constructor <;> intro h <;> linarith
    rw [if_neg hDc]
    rcases lt_or_gt_of_ne hnj_ne with hj' | hj'
    · rw [if_pos (hiff.mpr hj'), if_neg (not_lt.mpr hj'.le)]
      norm_num
    · rw [if_neg (fun h => absurd (hiff.mp h) (not_lt.mpr hj'.le)), if_pos hj']
      norm_num

/-! ## The target -/

/-- **The tangent frame signs**: for a closed oriented smooth `8`-manifold `V` there are signs
`frameSign V i x ∈ {±1}`, continuous on the chart sources of the finite cover
`Work.Thom.chartCover`, whose product at a common point of two charts is the sign of the transition
Jacobian. -/
theorem tangentFrameSigns_aux (V : Man8) :
    ∃ δ : (i : ChartIdx V) → V.pt → ℝ,
      (∀ (i : ChartIdx V) (x : V.pt), δ i x = 1 ∨ δ i x = -1) ∧
      (∀ i, ContinuousOn (δ i) (src V i)) ∧
      (∀ (i j : ChartIdx V) (x : V.pt) (hi : x ∈ src V i) (hj : x ∈ src V j),
        δ i x * δ j x = Real.sign (LinearMap.det (ContinuousLinearMap.toLinearMap
          (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x))))) := by
  refine ⟨frameSign V, ?_, ?_, ?_⟩
  · exact frameSign_eq_one_or_neg_one V
  · exact continuousOn_frameSign V
  · intro i j x hi hj
    exact frameSign_mul V i j hi hj

end

end Work.ThomBordism.FrameSigns
