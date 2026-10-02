import Mathlib
import Submission.Work.Milnor.Base

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open TopologicalSpace Set
open Submission.Milnor

/-- The inversion `x ↦ x / ‖x‖²` of `ℝ⁴` is continuous away from the origin. -/
lemma continuousAt_invBase {x : EuclideanSpace ℝ (Fin 4)} (hx : x ≠ 0) :
    ContinuousAt invBase x := by
  have h : ContinuousAt (fun y : EuclideanSpace ℝ (Fin 4) => ((‖y‖ : ℝ) ^ 2)⁻¹) x :=
    (continuous_norm.pow 2).continuousAt.inv₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  change ContinuousAt (fun y : EuclideanSpace ℝ (Fin 4) => ((‖y‖ : ℝ) ^ 2)⁻¹ • y) x
  exact h.smul continuousAt_id

/-- A neighbourhood of `0` on which `baseChart2` lands in a prescribed neighbourhood of `∞`.
Concretely, if `K` is compact then `baseChart2` maps a small ball around `0` into the complement
of the image of `K` in `S⁴ = ℝ⁴ ∪ {∞}`. -/
lemma baseChart2_preimage_mem_nhds_zero {K : Set (EuclideanSpace ℝ (Fin 4))} (hK : IsCompact K) :
    baseChart2 ⁻¹' (OnePoint.some '' Kᶜ ∪ {OnePoint.infty}) ∈
      𝓝 (0 : EuclideanSpace ℝ (Fin 4)) := by
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  refine Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 4))
      (show (0 : ℝ) < (R + 1)⁻¹ by positivity)) ?_
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [baseChart2_zero]
  · rw [mem_preimage, baseChart2, if_neg hx0, mem_union]
    left
    refine ⟨invBase x, ?_, rfl⟩
    rw [mem_compl_iff]
    intro hmem
    have h1 : ‖invBase x‖ = (‖x‖)⁻¹ := norm_invBase x
    have h2 : R + 1 < ‖invBase x‖ := by
      rw [h1]
      have ha : 0 < (R + 1)⁻¹ := by positivity
      have hb : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have h3 : ((R + 1)⁻¹)⁻¹ < (‖x‖)⁻¹ := (inv_lt_inv₀ ha hb).mpr hx
      rwa [inv_inv] at h3
    have h4 : ‖invBase x‖ ≤ R := hR _ hmem
    linarith

/-- The contribution of the second chart to the base map is continuous: the inversion
`x ↦ x/‖x‖²` extends continuously to `S⁴ = ℝ⁴ ∪ {∞}` by sending `0` to `∞`. -/
lemma continuous_baseChart2 :
    Continuous (baseChart2 : EuclideanSpace ℝ (Fin 4) → S4) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, baseChart2_zero]
    refine (OnePoint.le_nhds_infty
      (f := Filter.map baseChart2 (𝓝 (0 : EuclideanSpace ℝ (Fin 4))))).mpr ?_
    intro K _ hK
    rw [Filter.mem_map]
    exact baseChart2_preimage_mem_nhds_zero hK
  · have hc : ContinuousAt (fun y : EuclideanSpace ℝ (Fin 4) => (↑(invBase y) : S4)) x :=
      OnePoint.continuous_coe.continuousAt.comp (continuousAt_invBase hx)
    refine hc.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [baseChart2, if_neg hy]

/-- The underlying map on the disjoint union of two copies of `MSpace` is continuous. -/
lemma continuous_baseMapFun (k : ℤ) : Continuous (baseMapFun k) := by
  have h1 : Continuous (fun p : MSpace => (↑p.1 : S4)) :=
    OnePoint.continuous_coe.comp continuous_fst
  have h2 : Continuous (fun p : MSpace => baseChart2 p.1) :=
    continuous_baseChart2.comp continuous_fst
  exact Continuous.sumElim h1 h2

theorem continuous_baseMap (k : ℤ) : Continuous (baseMap k) :=
  (continuous_baseMapFun k).quotient_lift (fun _a _b h => baseMapFun_respects k h)

end Work.Milnor
