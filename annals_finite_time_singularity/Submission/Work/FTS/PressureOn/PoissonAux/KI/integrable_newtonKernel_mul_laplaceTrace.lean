import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Green.integrableOn_newtonKernel_ball
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric

namespace Work.FTS.PressureOn.PoissonAux.KI

/-- The Newtonian kernel is non-negative: `N z = (4π‖z‖)⁻¹ ≥ 0`. -/
lemma newtonKernel_nonneg (z : R3) : 0 ≤ newtonKernel z := by
  rw [Work.FTS.PressureOn.newtonKernel]; positivity

/-- **Integrability of the Newtonian kernel times the Laplacian trace of a compactly supported
`C²` function.**

`laplaceTrace ψ` is continuous (`Green.continuous_laplaceTrace`) and vanishes off `tsupport ψ`
(`Green.laplaceTrace_eq_zero_of_notMem_tsupport`), so it is bounded, say by `M`; the product is
then dominated by `M · N`, which is integrable on a ball containing `tsupport ψ` in dimension
three (`Green.integrableOn_newtonKernel_ball`, the borderline `‖z‖⁻¹` case).  Since the product
vanishes off that ball, `IntegrableOn` on the ball upgrades to global `Integrable`. -/
theorem integrable_newtonKernel_mul_laplaceTrace {ψ : R3 → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun x : R3 => newtonKernel x * laplaceTrace ψ x) := by
  have hcont : Continuous (laplaceTrace ψ) := Green.continuous_laplaceTrace ψ hψ
  -- `laplaceTrace ψ` is bounded: it is continuous and vanishes off `tsupport ψ`
  obtain ⟨M, hM⟩ := hcs.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  have hbound : ∀ z : R3, ‖laplaceTrace ψ z‖ ≤ max M 0 := by
    intro z
    by_cases hz : z ∈ tsupport ψ
    · exact le_trans (hM z hz) (le_max_left M 0)
    · rw [Green.laplaceTrace_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right M 0
  -- a ball containing the support of `ψ`
  obtain ⟨r, hr⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : R3)
  have hball : tsupport ψ ⊆ Metric.ball (0 : R3) (|r| + 1) := fun z hz =>
    Metric.closedBall_subset_ball (by linarith [le_abs_self r]) (hr hz)
  -- the dominating function: a multiple of the Newtonian kernel, integrable on the ball
  have hIntOn : IntegrableOn (fun z : R3 => (max M 0) * newtonKernel z)
      (Metric.ball (0 : R3) (|r| + 1)) volume :=
    (Green.integrableOn_newtonKernel_ball (|r| + 1)).const_mul (max M 0)
  have hmono : IntegrableOn (fun z : R3 => newtonKernel z * laplaceTrace ψ z)
      (Metric.ball (0 : R3) (|r| + 1)) volume := by
    refine Integrable.mono' hIntOn
      ((Green.measurable_newtonKernel.mul hcont.measurable).aestronglyMeasurable) ?_
    filter_upwards with z
    have hnk : 0 ≤ newtonKernel z := newtonKernel_nonneg z
    have h1 : ‖newtonKernel z * laplaceTrace ψ z‖ = newtonKernel z * ‖laplaceTrace ψ z‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnk, Real.norm_eq_abs]
    rw [h1]
    calc newtonKernel z * ‖laplaceTrace ψ z‖
        ≤ newtonKernel z * max M 0 := mul_le_mul_of_nonneg_left (hbound z) hnk
      _ = max M 0 * newtonKernel z := by ring
  -- the integrand vanishes off the ball
  exact hmono.integrable_of_forall_notMem_eq_zero fun x hx => by
    have hx' : x ∉ tsupport ψ := fun h => hx (hball h)
    rw [Green.laplaceTrace_eq_zero_of_notMem_tsupport hx', mul_zero]

end Work.FTS.PressureOn.PoissonAux.KI
