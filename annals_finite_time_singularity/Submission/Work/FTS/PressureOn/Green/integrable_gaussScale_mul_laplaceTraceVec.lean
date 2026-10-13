/-
# Integrability of the Gaussian scale times the Laplacian trace

The Newtonian kernel is the `s`-integral of the Gaussian scale,
`newtonKernel z = (2π√π)⁻¹ ∫_0^∞ exp(-(s²‖z‖²)) ds` (`newtonKernel_eq_integral_exp_neg`).
This file records that the product of that Gaussian scale with the *Laplacian trace*
`laplaceTraceVec G` of a compactly supported `C²` field is integrable.  The two ingredients are

* the Gaussian scale is `≍ ‖z‖⁻¹` (for `z ≠ 0`), so the product is dominated by
  `C ‖z‖⁻¹ ‖laplaceTraceVec G z‖` — integrable near the origin in dimension three;
* `laplaceTraceVec G` is continuous with compact support (its support is contained in
  `tsupport G`), so it is bounded and vanishes off any ball containing `tsupport G`.

The dominating function is the (continuous, a.e. equal) multiple
`(2π√π ‖laplaceTraceVec G‖_∞) * newtonKernel` of the Newtonian kernel, whose integrability on a
ball in `ℝ³` is `integrableOn_newtonKernel_ball`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Green.newtonKernel_eq_integral_exp_neg
import Submission.Work.FTS.PressureOn.Green.integrableOn_newtonKernel_ball

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Metric
open Work.FTS.PressureOn (laplaceTraceVec R3 newtonKernel)

namespace Work.FTS.PressureOn.Green

/-- **The Laplacian trace of a `C²` field is continuous.**  Each coordinate
`∂ᵢ∂ᵢ G = fderiv (fun w => fderiv G w (e i)) · (e i)` is continuous because the derivative of the
`C¹` slice `fun w => fderiv ℝ G w (e i)` is continuous (`ContDiff ℝ 0` and then `Continuous`). -/
theorem continuous_laplaceTraceVec (G : R3 → R3) (hG : ContDiff ℝ 2 G) :
    Continuous (laplaceTraceVec G) := by
  have hLdiff : ContDiff ℝ 0 (laplaceTraceVec G) := by
    unfold laplaceTraceVec
    apply ContDiff.sum
    intro i _
    have h1 : ContDiff ℝ 1 (fun w : R3 => fderiv ℝ G w (FiniteTimeSingularity.e i)) := by
      have h := hG.fderiv_right (m := 1) (by norm_num)
      exact h.clm_apply contDiff_const
    have h2 : ContDiff ℝ 0 (fun p : R3 × R3 =>
        (fderiv ℝ (fun w : R3 => fderiv ℝ G w (FiniteTimeSingularity.e i)) p.1) p.2) :=
      h1.contDiff_fderiv_apply (m := 0) (by norm_num)
    exact h2.comp (contDiff_id.prodMk contDiff_const)
  exact hLdiff.continuous

/-- **The support of the Laplacian trace is contained in the topological support of the field.**
Off `tsupport G` the field is eventually zero, hence so is each slice `fderiv ℝ G · (e i)`
(`tsupport_fderiv_apply_subset`), hence so is its derivative (`fderiv_of_notMem_tsupport`).  No
smoothness is needed for this statement. -/
theorem support_laplaceTraceVec_subset (G : R3 → R3) :
    Function.support (laplaceTraceVec G) ⊆ tsupport G := by
  intro z hz
  by_contra hzG
  apply hz
  unfold laplaceTraceVec
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : tsupport (fun w : R3 => fderiv ℝ G w (FiniteTimeSingularity.e i)) ⊆ tsupport G :=
    tsupport_fderiv_apply_subset ℝ (FiniteTimeSingularity.e i)
  have h2 : z ∉ tsupport (fun w : R3 => fderiv ℝ G w (FiniteTimeSingularity.e i)) :=
    fun h => hzG (h1 h)
  have h3 : fderiv ℝ (fun w : R3 => fderiv ℝ G w (FiniteTimeSingularity.e i)) z = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) h2
  simp [h3]

/-- **Integrability of the Gaussian scale times the Laplacian trace of a compactly supported `C²`
field.**

For `z ≠ 0` the Gaussian scale is exactly `√π/(2‖z‖) = 2π√π · newtonKernel z`
(`newtonKernel_eq_integral_exp_neg`), so the integrand is a.e. equal to
`2π√π · newtonKernel z · ‖laplaceTraceVec G z‖`.  That function is measurable, bounded by
`2π√π · ‖laplaceTraceVec G‖_∞ · newtonKernel z` everywhere, and vanishes off any ball containing
`tsupport G`; since `newtonKernel` is integrable on a ball in `ℝ³`
(`integrableOn_newtonKernel_ball`, the borderline `d = 3`, `α = 1` case), the integrand is
integrable. -/
theorem integrable_gaussScale_mul_laplaceTraceVec (G : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hG : ContDiff ℝ 2 G) (hcs : HasCompactSupport G) :
    MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 =>
      (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(s ^ 2 * ‖z‖ ^ 2)))
        * ‖Work.FTS.PressureOn.laplaceTraceVec G z‖) := by
  have hLcont : Continuous (laplaceTraceVec G) := continuous_laplaceTraceVec G hG
  have hLsupp : Function.support (laplaceTraceVec G) ⊆ tsupport G :=
    support_laplaceTraceVec_subset G
  -- the Laplacian trace of a compactly supported field is bounded
  have hLcs : IsCompact (Set.range (laplaceTraceVec G)) :=
    isCompact_range_of_support_subset_isCompact hLcont hcs.isCompact hLsupp
  obtain ⟨M, hM⟩ := hLcs.exists_bound_of_continuousOn continuous_id.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM (laplaceTraceVec G 0) (Set.mem_range_self 0))
  -- a ball containing `tsupport G`
  obtain ⟨r, hr⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : R3)
  have hball : tsupport G ⊆ Metric.ball (0 : R3) (|r| + 1) := fun z hz =>
    Metric.closedBall_subset_ball (by linarith [le_abs_self r]) (hr hz)
  -- the dominating function: a multiple of the Newtonian kernel, integrable on the ball
  have hIntOn : IntegrableOn (fun z : R3 => (2 * Real.pi * Real.sqrt Real.pi * M) * newtonKernel z)
      (Metric.ball (0 : R3) (|r| + 1)) volume :=
    (integrableOn_newtonKernel_ball (|r| + 1)).const_mul _
  -- the a.e. closed form of the integrand
  have hF2meas : Measurable (fun z : R3 =>
      2 * Real.pi * Real.sqrt Real.pi * newtonKernel z * ‖laplaceTraceVec G z‖) :=
    (measurable_newtonKernel.const_mul _).mul hLcont.norm.measurable
  have hF2int : IntegrableOn (fun z : R3 =>
      2 * Real.pi * Real.sqrt Real.pi * newtonKernel z * ‖laplaceTraceVec G z‖)
      (Metric.ball (0 : R3) (|r| + 1)) volume := by
    refine Integrable.mono' hIntOn hF2meas.aestronglyMeasurable ?_
    filter_upwards with z
    have hnk : 0 ≤ newtonKernel z := by
      rw [Work.FTS.PressureOn.newtonKernel]; positivity
    have hnn : (0:ℝ) ≤ 2 * Real.pi * Real.sqrt Real.pi * newtonKernel z :=
      mul_nonneg (by positivity) hnk
    calc ‖2 * Real.pi * Real.sqrt Real.pi * newtonKernel z * ‖laplaceTraceVec G z‖‖
        = 2 * Real.pi * Real.sqrt Real.pi * newtonKernel z * ‖laplaceTraceVec G z‖ :=
          Real.norm_of_nonneg (mul_nonneg hnn (norm_nonneg _))
      _ ≤ 2 * Real.pi * Real.sqrt Real.pi * newtonKernel z * M :=
          mul_le_mul_of_nonneg_left (hM (laplaceTraceVec G z) (Set.mem_range_self z)) hnn
      _ = (2 * Real.pi * Real.sqrt Real.pi * M) * newtonKernel z := by ring
  have haeeq : (fun z : R3 => (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(s ^ 2 * ‖z‖ ^ 2)))
        * ‖laplaceTraceVec G z‖)
      =ᵐ[volume] (fun z : R3 =>
        2 * Real.pi * Real.sqrt Real.pi * newtonKernel z * ‖laplaceTraceVec G z‖) := by
    have hne : ∀ᵐ z : R3 ∂volume, z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      have : {z : R3 | ¬z ≠ 0} = {0} := by ext z; simp
      rw [this]
      exact measure_singleton 0
    filter_upwards [hne] with z hz
    have hk := newtonKernel_eq_integral_exp_neg z hz
    have hc : (2 * Real.pi * Real.sqrt Real.pi) ≠ 0 := by positivity
    rw [hk, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  -- the closed form vanishes off the ball
  have hF2zero : ∀ z : R3, z ∉ Metric.ball (0 : R3) (|r| + 1) →
      (fun z : R3 => 2 * Real.pi * Real.sqrt Real.pi * newtonKernel z * ‖laplaceTraceVec G z‖) z = 0 := by
    intro z hz
    have hzG : z ∉ tsupport G := fun h => hz (hball h)
    have hLz : laplaceTraceVec G z = 0 := Function.notMem_support.mp (fun h => hzG (hLsupp h))
    simp [hLz]
  have hind : Integrable ((Metric.ball (0 : R3) (|r| + 1)).indicator
      (fun z : R3 => 2 * Real.pi * Real.sqrt Real.pi * newtonKernel z * ‖laplaceTraceVec G z‖)) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hF2int
  have hF2int' : Integrable (fun z : R3 =>
      2 * Real.pi * Real.sqrt Real.pi * newtonKernel z * ‖laplaceTraceVec G z‖) volume :=
    hind.congr (Filter.EventuallyEq.of_eq (by
      funext z
      by_cases hz : z ∈ Metric.ball (0 : R3) (|r| + 1)
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        exact (hF2zero z hz).symm))
  exact hF2int'.congr haeeq.symm

end Work.FTS.PressureOn.Green
