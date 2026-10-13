import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Topology.Constructible
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal

namespace Work.FTS.BSSwirl

theorem integrable_inv_norm_smul {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} {R M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) (u : Work.FTS.BSSwirl.R3) :
    MeasureTheory.Integrable (fun y => (‖u - y‖)⁻¹ • ω y) MeasureTheory.volume := by
  -- `‖·‖⁻¹` is locally integrable in dimension `3`, being dominated by `‖·‖ ^ (-1)`.
  have hbase : LocallyIntegrable (fun z : R3 => (‖z‖)⁻¹) volume := by
    refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ ?_
    · simp
    · simp
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), Real.rpow_neg_one,
        one_mul]
    · exact (Measurable.inv measurable_norm).aestronglyMeasurable
  -- translation invariance moves the singularity from `0` to `u`
  have htrans : LocallyIntegrable (fun z : R3 => (‖u - z‖)⁻¹) volume := by
    let e : R3 ≃ₜ R3 :=
      { toFun := fun z => z - u
        invFun := fun z => z + u
        left_inv := fun z => by simp
        right_inv := fun z => by simp
        continuous_toFun := continuous_id.sub continuous_const
        continuous_invFun := continuous_id.add continuous_const }
    have hmap : Measure.map (⇑e) volume = volume := by
      have h := Measure.IsAddRightInvariant.map_add_right_eq_self (μ := (volume : Measure R3)) (-u)
      simpa [e, sub_eq_add_neg] using h
    have h1 : LocallyIntegrable (fun w : R3 => (‖w‖)⁻¹) (Measure.map (⇑e) volume) := by
      rw [hmap]; exact hbase
    have h2 := (locallyIntegrable_map_homeomorph e).mp h1
    have hae : ((fun w : R3 => (‖w‖)⁻¹) ∘ ⇑e) =ᵐ[volume] (fun z : R3 => (‖u - z‖)⁻¹) := by
      filter_upwards with z
      show (‖e z‖)⁻¹ = (‖u - z‖)⁻¹
      rw [show e z = z - u from rfl, norm_sub_rev]
    exact h2.congr hae
  -- hence it is integrable on the compact support ball
  have hIntBall : IntegrableOn (fun z : R3 => (‖u - z‖)⁻¹) (Metric.closedBall (0 : R3) R)
      volume := by
    have hbig : IntegrableOn (fun z : R3 => (‖u - z‖)⁻¹)
        (Metric.closedBall u (|R| + ‖u‖ + 1)) volume :=
      htrans.integrableOn_isCompact (isCompact_closedBall u _)
    refine hbig.mono_set ?_
    intro y hy
    rw [Metric.mem_closedBall] at hy ⊢
    have h2 : dist 0 u = ‖u‖ := dist_zero_left u
    have habs : R ≤ |R| := le_abs_self R
    linarith [dist_triangle y 0 u, hy, habs, norm_nonneg u, h2]
  have hf_meas : AEStronglyMeasurable (fun y : R3 => (‖u - y‖)⁻¹ • ω y)
      (volume.restrict (Metric.closedBall (0 : R3) R)) := by
    have hm : Measurable (fun y : R3 => (‖u - y‖)⁻¹) :=
      (measurable_const.sub measurable_id).norm.inv
    exact (hm.aestronglyMeasurable.restrict).smul hmeas.restrict
  have hg : Integrable (fun y : R3 => M * (‖u - y‖)⁻¹)
      (volume.restrict (Metric.closedBall (0 : R3) R)) :=
    hIntBall.const_mul M
  have hbound : ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : R3) R)),
      ‖(‖u - y‖)⁻¹ • ω y‖ ≤ M * (‖u - y‖)⁻¹ := by
    filter_upwards with y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    calc (‖u - y‖)⁻¹ * ‖ω y‖ ≤ (‖u - y‖)⁻¹ * M :=
          mul_le_mul_of_nonneg_left (hbdd y) (inv_nonneg.mpr (norm_nonneg _))
      _ = M * (‖u - y‖)⁻¹ := by ring
  have hIntOn : IntegrableOn (fun y : R3 => (‖u - y‖)⁻¹ • ω y) (Metric.closedBall (0 : R3) R)
      volume :=
    Integrable.mono' hg hf_meas hbound
  -- the integrand vanishes off the ball, so `IntegrableOn` upgrades to `Integrable`
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hIntOn
  intro y hy
  rw [Function.mem_support] at hy
  exact hsupp y (fun h => hy (by rw [h, smul_zero]))

end Work.FTS.BSSwirl
