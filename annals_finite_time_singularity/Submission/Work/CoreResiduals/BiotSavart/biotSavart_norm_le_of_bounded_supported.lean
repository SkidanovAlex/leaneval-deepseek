import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.norm_bsField_diff_bound
import Submission.Work.StabilityFar.Decay.norm_crossL_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `biotSavart_norm_le_of_bounded_supported`

A *sharp* near-field (indeed everywhere) bound for the Biot–Savart field of a vorticity that is
bounded by `M ≥ 0` and supported in `B(0,R)`: for **every** point `x`,

  `‖biotSavart ω x‖ ≤ M * (‖x‖ + R + 1)`.

The point of the estimate is that the constant is linear in `‖x‖ + R` rather than a fixed
multiple of `R` (as in `Work.LWP.BiotSavart.nearField_bound`, which gives `3 M R`): the support
`B(0,R)` lies in the ball of radius `‖x‖ + R` about `x`, so

  `‖biotSavart ω x‖ ≤ (4π)⁻¹ M ∫_{‖y‖≤R} ‖x-y‖⁻² dy ≤ (4π)⁻¹ M · 4π(‖x‖ + R) = M (‖x‖ + R)`,

using `∫_{B(x,r)} ‖z - x‖⁻² dz = 4π r` (`inv_sq_lintegral_closedBall_shifted_le`), the
dimensional borderline case `s = -2` in which the kernel singularity exactly cancels the
spherical Jacobian.
-/

open MeasureTheory Metric
open scoped Topology ENNReal

namespace Work.CoreResiduals.BiotSavart

/-- **The scalar near-field weight, centred at the origin.**  For a vorticity supported in
`B(0,R)` the singular weight `‖x - y‖⁻²` is integrated against the ball `B(0,R)`, which is
contained in the ball of radius `‖x‖ + R` about `x`; the shifted ball integral
`Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_shifted_le` then bounds it by `4π(‖x‖ + R)`. -/
theorem inv_sq_lintegral_closedBall_origin_le {R : ℝ} (hR : 0 ≤ R) (x : Work.LWP.R3) :
    ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (4 * Real.pi * (‖x‖ + R)) := by
  have hsub : Metric.closedBall (0 : Work.LWP.R3) R ⊆ Metric.closedBall x (‖x‖ + R) := by
    intro y hy
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy ⊢
    calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := by linarith
      _ = ‖x‖ + R := by ring
  calc ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      = ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R,
          ENNReal.ofReal ((‖y - x‖ ^ (2 : ℕ))⁻¹) := by
        apply lintegral_congr
        intro y
        rw [norm_sub_rev]
    _ ≤ ∫⁻ y in Metric.closedBall x (‖x‖ + R), ENNReal.ofReal ((‖y - x‖ ^ (2 : ℕ))⁻¹) :=
        lintegral_mono_set hsub
    _ ≤ ENNReal.ofReal (4 * Real.pi * (‖x‖ + R)) :=
        Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_shifted_le x (by positivity)

/-- **The `L¹` estimate for the Biot–Savart integrand, with a free constant.**  If `ω` is bounded
by `M ≥ 0` and supported in `B(0,R)`, and if the scalar weight `‖x - y‖⁻²` has integral at most
`A` over that ball, then the `ℝ³`-valued integrand has integral at most `M · A`:

  `∫⁻ y, ‖(‖x-y‖³)⁻¹ • (ω y × (x-y))‖ ≤ M · A`.

This is `Work.LWP.BiotSavart.lintegral_bsIntegrand_le` with the particular value `12πR` of `A`
replaced by an arbitrary bound, which is what the linear-in-`‖x‖` estimate requires. -/
theorem lintegral_bsIntegrand_le_mul {ω : Work.LWP.R3 → Work.LWP.R3} {R M A : ℝ} (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (x : Work.LWP.R3)
    (hscal : ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R,
        ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) ≤ ENNReal.ofReal A) :
    ∫⁻ y, ENNReal.ofReal ‖Work.LWP.BiotSavart.bsIntegrand ω x y‖
      ≤ ENNReal.ofReal (M * A) := by
  classical
  have hsmeas : MeasurableSet (Metric.closedBall (0 : Work.LWP.R3) R) :=
    Metric.isClosed_closedBall.measurableSet
  have hpoint : ∀ y, ENNReal.ofReal ‖Work.LWP.BiotSavart.bsIntegrand ω x y‖
      ≤ (Metric.closedBall (0 : Work.LWP.R3) R).indicator
          (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : Work.LWP.R3) R
    · rw [Set.indicator_of_mem hy, ← ENNReal.ofReal_mul hM]
      exact ENNReal.ofReal_le_ofReal (Work.LWP.BiotSavart.bsIntegrand_norm_le hM hω x y)
    · rw [Set.indicator_of_notMem hy]
      have hωy : ω y = 0 := by
        by_contra hne
        exact hy (hsupp y hne)
      simp [Work.LWP.BiotSavart.bsIntegrand, hωy]
  have hsplit : (fun y => (Metric.closedBall (0 : Work.LWP.R3) R).indicator
        (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y)
      = fun y => ENNReal.ofReal M * (Metric.closedBall (0 : Work.LWP.R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0 : Work.LWP.R3) R <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  calc ∫⁻ y, ENNReal.ofReal ‖Work.LWP.BiotSavart.bsIntegrand ω x y‖
      ≤ ∫⁻ y, (Metric.closedBall (0 : Work.LWP.R3) R).indicator
          (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y :=
        lintegral_mono hpoint
    _ = ∫⁻ y, ENNReal.ofReal M * (Metric.closedBall (0 : Work.LWP.R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by rw [hsplit]
    _ = ENNReal.ofReal M * ∫⁻ y, (Metric.closedBall (0 : Work.LWP.R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal M * ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R,
          ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) := by
        rw [lintegral_indicator hsmeas]
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal A := mul_le_mul_right hscal _
    _ = ENNReal.ofReal (M * A) := by rw [← ENNReal.ofReal_mul hM]

theorem biotSavart_norm_le_of_bounded_supported {ω : Work.LWP.R3 → Work.LWP.R3} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hω : ∀ a, ‖ω a‖ ≤ M)
    (hsupp : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) (x : Work.LWP.R3) :
    ‖Work.LWP.biotSavart ω x‖ ≤ M * (‖x‖ + R + 1) := by
  have hR0 : 0 ≤ R := le_of_lt hR
  set A : ℝ := ‖x‖ + R with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hscal : ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R,
      ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) ≤ ENNReal.ofReal (4 * Real.pi * A) := by
    rw [hA]
    exact inv_sq_lintegral_closedBall_origin_le hR0 x
  have hInt := lintegral_bsIntegrand_le_mul (A := 4 * Real.pi * A) hM hω hsupp x hscal
  have h1 : ‖∫ y, Work.LWP.BiotSavart.bsIntegrand ω x y‖
      ≤ (∫⁻ y, ENNReal.ofReal ‖Work.LWP.BiotSavart.bsIntegrand ω x y‖).toReal :=
    norm_integral_le_lintegral_norm _
  have h2 : (∫⁻ y, ENNReal.ofReal ‖Work.LWP.BiotSavart.bsIntegrand ω x y‖).toReal
      ≤ M * (4 * Real.pi * A) :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hInt).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  rw [Work.LWP.BiotSavart.biotSavart_eq_integral, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * Real.pi)⁻¹)]
  calc (4 * Real.pi)⁻¹ * ‖∫ y, Work.LWP.BiotSavart.bsIntegrand ω x y‖
      ≤ (4 * Real.pi)⁻¹ * (M * (4 * Real.pi * A)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ ≤ M * (‖x‖ + R + 1) := by
        rw [hA]
        have heq : (4 * Real.pi)⁻¹ * (M * (4 * Real.pi * (‖x‖ + R))) = M * (‖x‖ + R) := by
          field_simp
        rw [heq]
        nlinarith [hM, norm_nonneg x]

end Work.CoreResiduals.BiotSavart
