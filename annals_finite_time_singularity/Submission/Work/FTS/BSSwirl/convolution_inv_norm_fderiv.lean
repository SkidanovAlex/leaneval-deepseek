/-
# `Work.FTS.BSSwirl.convolution_inv_norm_fderiv` — differentiating the Newtonian potential

For a `C¹` function `k` with compact support on `ℝ³`, the (scalar) Newtonian potential

`y' ↦ ∫ t, ‖y' - t‖⁻¹ * k t`

is differentiable, and *its derivative is the potential of the derivative*:

`(fderiv ℝ (fun y' => ∫ t, ‖y' - t‖⁻¹ * k t) y) v = ∫ x, ‖x - y‖⁻¹ * (fderiv ℝ k x) v`.

This is the (commutative) convolution identity `∇(g ⋆ k) = g ⋆ ∇k` for the locally integrable
kernel `g = ‖·‖⁻¹`: no boundary term appears because `k` is compactly supported.

The proof is entirely through Mathlib's convolution calculus:

* `HasCompactSupport.hasFDerivAt_convolution_left` computes the total derivative of
  `k ⋆[lsmul ℝ ℝ] ‖·‖⁻¹` as `fderiv ℝ k ⋆[precompL ℝ³ (lsmul ℝ ℝ)] ‖·‖⁻¹` (no change of
  variables is needed on the function side, since `k t • ‖y' - t‖⁻¹ = ‖y' - t‖⁻¹ * k t`);
* `ContinuousLinearMap.integral_apply` pulls the evaluation at `v` out of the Bochner integral
  of the `ℝ³ →L[ℝ] ℝ`-valued convolution; the required integrability comes from
  `HasCompactSupport.convolutionExists_left` (`fderiv ℝ k` is continuous with compact support,
  the kernel is locally integrable);
* the two integrands then agree pointwise, using `‖y - t‖ = ‖t - y‖` and commutativity of
  multiplication in `ℝ`.

The only "analysis" input is the local integrability of `‖·‖⁻¹` on `ℝ³`, which follows from
`MeasureTheory.locallyIntegrable_of_norm_le_rpow` (the singularity `‖z‖⁻¹` is summable in
dimension `3`).  No change of variables under the integral is required anywhere.
-/
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Convolution Topology

namespace Work.FTS.BSSwirl

noncomputable section

/-- The Newtonian kernel `z ↦ ‖z‖⁻¹` is locally integrable on `ℝ³`: in dimension `3` the
singularity at the origin is summable (`∫_{B(0,ρ)} ‖z‖⁻¹ dz = 2πρ² < ∞`). -/
theorem locallyIntegrable_inv_norm_kernel :
    LocallyIntegrable (fun z : R3 => (‖z‖)⁻¹) volume := by
  refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (f := fun z : R3 => (‖z‖)⁻¹)
    (C := 1) (α := 1) ?_ ?_ ?_ ?_
  · simp
  · simp
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), Real.rpow_neg_one,
      one_mul]
  · exact (Measurable.inv measurable_norm).aestronglyMeasurable

theorem convolution_inv_norm_fderiv {k : Work.FTS.BSSwirl.R3 → ℝ}
    (hk : ContDiff ℝ 1 k) (hc : HasCompactSupport k) (y v : Work.FTS.BSSwirl.R3) :
    (fderiv ℝ (fun y' : Work.FTS.BSSwirl.R3 => ∫ t, (‖y' - t‖)⁻¹ * k t) y) v
      = ∫ x, (‖x - y‖)⁻¹ * (fderiv ℝ k x) v := by
  have hMk : LocallyIntegrable (fun z : R3 => (‖z‖)⁻¹) volume :=
    locallyIntegrable_inv_norm_kernel
  -- The potential is the convolution of `k` with the Newtonian kernel.
  have hconv : (fun y' : R3 => ∫ t, (‖y' - t‖)⁻¹ * k t)
      = convolution k (fun z : R3 => (‖z‖)⁻¹) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y'
    rw [MeasureTheory.convolution_lsmul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [smul_eq_mul, mul_comm]
  -- Its derivative, as computed by the convolution calculus.
  have hderiv := hc.hasFDerivAt_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk hMk y
  -- Integrability of the `ℝ³ →L[ℝ] ℝ`-valued integrand, so that evaluation at `v` commutes
  -- with the integral.
  have hcf : HasCompactSupport (fderiv ℝ k) := hc.fderiv ℝ
  have hcont : Continuous (fderiv ℝ k) := hk.continuous_fderiv one_ne_zero
  have hex : ConvolutionExists (fderiv ℝ k) (fun z : R3 => (‖z‖)⁻¹)
      (ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ)) volume :=
    HasCompactSupport.convolutionExists_left _ hcf hcont hMk
  have hint : Integrable (fun t : R3 => (ContinuousLinearMap.precompL R3
      (ContinuousLinearMap.lsmul ℝ ℝ)) ((fderiv ℝ k) t) ((fun z : R3 => (‖z‖)⁻¹) (y - t)))
      volume := hex y
  -- Evaluate the derivative at `v` and identify the integrand.
  have hval : (convolution (fderiv ℝ k) (fun z : R3 => (‖z‖)⁻¹)
        (ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ)) volume y) v
      = ∫ x, (‖x - y‖)⁻¹ * (fderiv ℝ k x) v := by
    rw [MeasureTheory.convolution_def]
    rw [ContinuousLinearMap.integral_apply hint]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
      norm_sub_rev, mul_comm]
  rw [hconv, hderiv.fderiv, hval]

end

end Work.FTS.BSSwirl
