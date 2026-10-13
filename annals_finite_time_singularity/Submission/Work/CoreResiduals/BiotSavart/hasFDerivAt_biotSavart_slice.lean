import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_ball_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Filter
open scoped Topology

/-- **The `x`-derivative of the Biot–Savart field of a single slice.**  This is the pointwise form
of `Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one`: for a vorticity `ω` that is bounded,
supported in `closedBall 0 R`, ae-strongly-measurable and Hölder of exponent `c > 0`, the map
`x ↦ biotSavart ω x` is differentiable at every `x` with derivative `(4π)⁻¹ • bsDerivCLM ω ρ x`
for any `ρ > R + ‖x‖`.

Proof: exactly the body of `biotSavart_contDiff_one`, at the single point `x` instead of on a ball:
apply `holder_reduce` to get an exponent `c' < 1`, `hasFDerivAt_bsField` for the un-normalised
field `bsField ω ρ` (valid because `R + ‖x‖ < ρ`), multiply by the constant `(4π)⁻¹`, and rewrite
`biotSavart ω = (4π)⁻¹ • bsField ω ρ` on a neighbourhood of `x` via `biotSavart_ball_integral`
(`HasFDerivAt.congr_of_eventuallyEq`). -/
theorem hasFDerivAt_biotSavart_slice {ω : Work.CoreResiduals.R3 → Work.CoreResiduals.R3}
    {R M C c ρ : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hc : 0 < c)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hhold : ∀ a b : Work.CoreResiduals.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    {x : Work.CoreResiduals.R3} (hρ : R + ‖x‖ < ρ) :
    HasFDerivAt (Work.LWP.biotSavart ω)
      ((4 * Real.pi)⁻¹ • Work.CoreResiduals.BiotSavart.bsDerivCLM ω ρ x) x := by
  -- Reduce the Hölder exponent below `1`, as in `biotSavart_contDiff_one`.
  obtain ⟨c', C', hc'0, hc'1, hC'0, hhold'⟩ := holder_reduce hc hM hbdd hhold
  -- Differentiability of the un-normalised field `bsField ω ρ` at the single point `x`.
  have hd : HasFDerivAt (bsField ω ρ) (bsDerivCLM ω ρ x) x :=
    hasFDerivAt_bsField hR hM hc'0 hc'1 hC'0 hbdd hs hm hhold' hρ
  -- Multiply the field and its derivative by the normalisation constant `(4π)⁻¹`.
  have hd2 : HasFDerivAt ((4 * Real.pi)⁻¹ • bsField ω ρ)
      ((4 * Real.pi)⁻¹ • bsDerivCLM ω ρ x) x := hd.const_smul _
  -- On a neighbourhood of `x` the Biot–Savart field agrees with the normalised `bsField`.
  refine hd2.congr_of_eventuallyEq ?_
  have hcont : ContinuousAt (fun y : R3 => R + ‖y‖) x :=
    continuousAt_const.add continuous_norm.continuousAt
  have hev : ∀ᶠ y in 𝓝 x, R + ‖y‖ < ρ := hcont.eventually_lt continuousAt_const hρ
  filter_upwards [hev] with y hy
  exact biotSavart_ball_integral hM hbdd hs hm (le_of_lt hy)

end Work.CoreResiduals.BiotSavart
