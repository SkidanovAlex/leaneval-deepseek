/-
# `Work.FTS.BSSwirl.Book` — bookkeeping for `HolderWith` hypotheses and compact support

This module turns the two hypotheses of item 7a of the lead's design (`HolderWith C α ω` and the
support condition `ω x ≠ 0 → ‖x‖ ≤ R`) into the shapes consumed by the analytic lemmas of the
area:

* `holderWith_dist_le` — the pointwise form `‖ω a - ω b‖ ≤ C ‖a-b‖^α`;
* `exists_bound_of_holderWith_support` — `ω` is bounded (continuity on a compact ball);
* `eq_zero_of_holderWith_support_le` — if the support radius is `≤ 0` then `ω ≡ 0`;
* `continuous_of_holderWith`, `aestronglyMeasurable_of_holderWith`.

The `dist`-form is the shape required by the workspace's Calderón–Zygmund chapter
(`Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one`), and the boundedness is what makes the
Newtonian potential well defined.
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory Bornology
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- **`HolderWith` in pointwise norm form.** -/
theorem holderWith_dist_le {C α : ℝ≥0} {ω : R3 → R3} (h : HolderWith C α ω) (a b : R3) :
    ‖ω a - ω b‖ ≤ (C : ℝ) * ‖a - b‖ ^ ((α : ℝ≥0) : ℝ) := by
  simpa [dist_eq_norm] using h.dist_le a b

/-- A `HolderWith` field of positive exponent is continuous. -/
theorem continuous_of_holderWith {C α : ℝ≥0} {ω : R3 → R3} (h : HolderWith C α ω)
    (hα : 0 < (α : ℝ)) : Continuous ω :=
  h.continuous hα

/-- A `HolderWith` field of positive exponent is a.e. strongly measurable. -/
theorem aestronglyMeasurable_of_holderWith {C α : ℝ≥0} {ω : R3 → R3} (h : HolderWith C α ω)
    (hα : 0 < (α : ℝ)) : AEStronglyMeasurable ω volume :=
  (h.continuous hα).aestronglyMeasurable

/-- **A pointwise Hölder bound gives continuity**, for a positive exponent. -/
theorem continuous_of_holder_pointwise {ω : R3 → R3} {C α : ℝ} (hα : 0 < α)
    (h : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ α) : Continuous ω := by
  have h' : ∀ a b : R3, ‖ω a - ω b‖ ≤ (max C 0 + 1) * ‖a - b‖ ^ α := fun a b =>
    le_trans (h a b) (mul_le_mul_of_nonneg_right (by linarith [le_max_left C 0])
      (Real.rpow_nonneg (norm_nonneg _) _))
  rw [Metric.continuous_iff]
  rintro x ε hε
  have hM : 0 < max C 0 + 1 := by linarith [le_max_right C 0]
  refine ⟨(ε / (max C 0 + 1)) ^ (1 / α), Real.rpow_pos_of_pos (div_pos hε hM) _, ?_⟩
  intro y hy
  have hy' : ‖y - x‖ < (ε / (max C 0 + 1)) ^ (1 / α) := by simpa [dist_eq_norm] using hy
  have h2 : ‖y - x‖ ^ α < ε / (max C 0 + 1) := by
    calc ‖y - x‖ ^ α < ((ε / (max C 0 + 1)) ^ (1 / α)) ^ α :=
          Real.rpow_lt_rpow (norm_nonneg _) hy' hα
      _ = ε / (max C 0 + 1) := by
          rw [← Real.rpow_mul (le_of_lt (div_pos hε hM)) (1 / α) α, one_div,
            inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one]
  calc dist (ω y) (ω x) = ‖ω y - ω x‖ := dist_eq_norm _ _
    _ ≤ (max C 0 + 1) * ‖y - x‖ ^ α := h' y x
    _ < (max C 0 + 1) * (ε / (max C 0 + 1)) := mul_lt_mul_of_pos_left h2 hM
    _ = ε := by field_simp

/-- **Boundedness of a `HolderWith` field with compactly supported values.**  A continuous field
vanishing off `closedBall 0 R` is bounded by the maximum of its norm over the (compact) ball of
radius `max R 0`. -/
theorem exists_bound_of_holderWith_support {C α : ℝ≥0} {ω : R3 → R3} {R : ℝ}
    (hα : 0 < (α : ℝ)) (h : HolderWith C α ω) (hsupp : ∀ x, ω x ≠ 0 → ‖x‖ ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖ω x‖ ≤ M := by
  have hcont : Continuous ω := h.continuous hα
  have hsub : ∀ x, ω x ≠ 0 → x ∈ Metric.closedBall (0 : R3) (max R 0) := fun x hx =>
    Metric.mem_closedBall.mpr (by
      rw [dist_zero_right]
      exact le_trans (hsupp x hx) (le_max_left R 0))
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_closedBall (0 : R3) (max R 0)).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self (le_max_right R 0)⟩ (hcont.continuousOn.norm)
  exact ⟨‖ω x₀‖, norm_nonneg _, fun x => by
    by_cases hx : ω x = 0
    · simp [hx]
    · exact hmax (hsub x hx)⟩

/-- **A `HolderWith` field whose support radius is `≤ 0` vanishes identically.**  It vanishes off
the origin by the support condition and at the origin by continuity. -/
theorem eq_zero_of_holderWith_support_le {C α : ℝ≥0} {ω : R3 → R3} {R : ℝ}
    (hα : 0 < (α : ℝ)) (h : HolderWith C α ω) (hsupp : ∀ x, ω x ≠ 0 → ‖x‖ ≤ R) (hR : R ≤ 0) :
    ∀ x, ω x = 0 := by
  have hcont : Continuous ω := h.continuous hα
  have hoff : ∀ x, x ≠ 0 → ω x = 0 := by
    intro x hx
    by_contra h0
    have h1 : ‖x‖ ≤ R := hsupp x h0
    have h2 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    linarith
  intro x
  by_cases hx : x = 0
  · subst hx
    have h1 : Tendsto ω (𝓝[≠] (0 : R3)) (𝓝 (ω 0)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto ω (𝓝[≠] (0 : R3)) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hoff y hy).symm
    exact tendsto_nhds_unique h1 h2
  · exact hoff x hx

end

end Work.FTS.BSSwirl
