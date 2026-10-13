/-
# The derivative kernel of the vector Newtonian potential is Bochner integrable

The Newtonian potential of a bounded, compactly supported vorticity `ω` is

  `A ω x = (4π)⁻¹ • ∫ y, ‖x-y‖⁻¹ • ω y`,

and its candidate derivative is the bounded-linear-map-valued integral

  `potDeriv ω x = (4π)⁻¹ • ∫ y, (‖x-y‖³)⁻¹ • (innerSL ℝ (y-x)).smulRight (ω y)`

(`Work.FTS.BSSwirl.potDeriv`).  This module proves that the integrand of `potDeriv` is Bochner
integrable, which is what makes that integral well defined and lets `hasFDerivAt_newtonPotential`
differentiate under the integral sign.

## The mathematics

The kernel `‖x-y‖⁻³` is *not* integrable in `ℝ³` (the borderline case `3 = dim`), and indeed the
integrand of `potDeriv` is singular at `y = x`.  It does not matter: the tensor factor
`(innerSL ℝ (y-x)).smulRight (ω y)` vanishes *linearly* in `y - x`, and

  `‖(innerSL ℝ (y-x)).smulRight (ω y)‖ = ‖y-x‖ · ‖ω y‖`,

so the whole integrand is dominated by `‖x-y‖⁻² ‖ω y‖ ≤ M ‖x-y‖⁻²`, an integrable singularity
(`2 < 3`).  The support hypothesis confines `ω` to the compact ball `B(0,R)`, so the dominating
function is `M ‖x-y‖⁻²` on that ball, whose integral is finite
(`Work.StabilityFar.Decay.integrable_indicator_inv_sq`).  Measurability of the
bounded-linear-map-valued integrand is the composition of the continuous map
`y ↦ smulRightL (innerSL ℝ (y-x))` with the ae-strongly-measurable `ω`, and is discharged by the
`measurability` tactic.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.StabilityFar.Decay.integrable_indicator_inv_sq
import Submission.Work.StabilityFar.Decay.KernelDefs

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

open MeasureTheory
open scoped Topology ENNReal

namespace Work.FTS.BSSwirl

/-- **Pointwise domination of the `potDeriv` kernel.**  The tensor `(‖x-y‖³)⁻¹ • innerSL(y-x) ⊗ ω y`
is bounded in norm by the (integrable) weight `M ‖x-y‖⁻²`, but only on the support ball `B(0,R)`;
off the support the vorticity vanishes and so does the integrand.  The algebraic content is
`(a³)⁻¹ · a = (a²)⁻¹`, valid for every real `a` including `a = 0` (both sides are `0` there). -/
theorem norm_inv_cube_smulRight_le {ω : R3 → R3} {M R : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) (x : R3) :
    ∀ y, ‖((‖x - y‖ ^ (3:ℕ))⁻¹ : ℝ) • (innerSL ℝ (y - x)).smulRight (ω y)‖
      ≤ (Metric.closedBall (0:R3) R).indicator (fun y => M * ((‖x - y‖ ^ (2:ℕ))⁻¹)) y := by
  have haux : ∀ a : ℝ, (a^3)⁻¹ * (a * M) = M * ((a^2)⁻¹) := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · field_simp
  intro y
  by_cases hw : ω y = 0
  · have h0 : (innerSL ℝ (y - x)).smulRight (ω y) = 0 := by rw [hw]; simp
    rw [h0, smul_zero, norm_zero]
    by_cases hy : y ∈ Metric.closedBall (0:R3) R
    · rw [Set.indicator_of_mem hy]
      exact mul_nonneg hM (inv_nonneg.mpr (by positivity))
    · rw [Set.indicator_of_notMem hy]
  · have hy : y ∈ Metric.closedBall (0:R3) R := hsupp y hw
    rw [Set.indicator_of_mem hy]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    calc (‖x - y‖ ^ (3:ℕ))⁻¹ * (‖y - x‖ * ‖ω y‖)
        ≤ (‖x - y‖ ^ (3:ℕ))⁻¹ * (‖y - x‖ * M) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hbdd y) (norm_nonneg _)
      _ = M * ((‖x - y‖ ^ (2:ℕ))⁻¹) := by
          rw [norm_sub_rev y x]
          exact haux ‖x - y‖

theorem integrable_inv_cube_smulRight {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} {M R : ℝ}
    (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) (x : Work.FTS.BSSwirl.R3) :
    MeasureTheory.Integrable
      (fun y : Work.FTS.BSSwirl.R3 =>
        ((‖x - y‖ ^ (3 : ℕ))⁻¹ : ℝ) • (innerSL ℝ (y - x)).smulRight (ω y))
      MeasureTheory.volume := by
  refine Integrable.mono' (Work.StabilityFar.Decay.integrable_indicator_inv_sq (R := R) x hM) ?_ ?_
  · first
    | exact ((((continuous_const.sub continuous_id).norm.pow 3).measurable.inv).aestronglyMeasurable).smul
            (Continuous.comp_aestronglyMeasurable₂ (ContinuousLinearMap.smulRightL ℝ Work.FTS.BSSwirl.R3 Work.FTS.BSSwirl.R3).continuous₂
              (((innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable) hmeas)
    | measurability
  · filter_upwards with y
    exact norm_inv_cube_smulRight_le hM hbdd hsupp x y

end Work.FTS.BSSwirl
