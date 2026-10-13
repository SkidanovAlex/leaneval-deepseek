import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.FTS.Apriori.Limit.SlotCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

/-- **The cut-off `ℋ⁴`-energy is bounded by the full `ℋ⁴`-energy.**

`HksqCut α f η = ∫∫_{Qμ} (HkIntegrand α 4 f) · η` is the `ℋ⁴`-integrand of `f` multiplied by a
cut-off `η` with `0 ≤ η ≤ 1`, integrated against the product measure `Qμ = dz dθ` on the closed
quadrant.  Since the integrand is nonnegative and `η ≤ 1`, the cut-off can only decrease the
integral, and `HkSq α 4 f = ∫_z ∫_θ HkIntegrand α 4 f` is the iterated integral of the very same
(uncut) integrand.

The two integrals live on different measures, so the bridge is Tonelli for the *Bochner*
integral (`MeasureTheory.integral_prod`): the cut-off integrand is continuous on the open
quadrant and supported in the compact `tsupport η ⊆ Qd`, hence integrable for `Qμ`; on each
`z`-slice the inner integral is then dominated by the uncut one, and `HkMem α 4 f` supplies the
integrability of the `z ↦ ∫_θ HkIntegrand α 4 f z θ` that `MeasureTheory.integral_mono_of_nonneg`
needs. -/
theorem HksqCut_le_HkSq {α : ℝ} {f η : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f) (hη : Work.FTS.Apriori.Limit.TestQ η)
    (h0 : ∀ z θ, 0 ≤ η z θ) (h1 : ∀ z θ, η z θ ≤ 1) :
    Work.FTS.Apriori.Limit.HksqCut α f η ≤ Work.Spaces.HkSq α 4 f := by
  -- The `ℋ⁴`-integrand is continuous on the open quadrant, being a sum of squares of slots.
  have hcontHk : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2) Qd := by
    rw [show (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
        = fun p : ℝ × ℝ => ∑ ji ∈ activeSlots, (slot α ji f p.1 p.2) ^ 2 from
      funext (fun p => HkIntegrand_eq_sum_slot α f p.1 p.2)]
    exact continuousOn_finsetSum _ (fun ji _ => (continuousOn_slot hf α ji).pow 2)
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2 * η p.1 p.2) Qd :=
    hcontHk.mul hη.1.continuousOn
  -- It is supported in the compact `tsupport η ⊆ Qd`, hence integrable for `Qμ`.
  have hGint : Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2 * η p.1 p.2) Qμ :=
    integrable_of_continuousOn_of_support hcont hη.2.1 hη.2.2
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport _))
  -- Tonelli: the product integral is the iterated integral.
  have hprod : (∫ p, Work.Spaces.HkIntegrand α 4 f p.1 p.2 * η p.1 p.2 ∂Qμ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f z θ * η z θ := by
    rw [Qμ]
    exact MeasureTheory.integral_prod _ hGint
  rw [HksqCut, hprod, Work.Spaces.HkSq]
  -- Monotonicity in `z` of the iterated integral.
  refine MeasureTheory.integral_mono_of_nonneg ?_ hmem.2 ?_
  · exact Filter.Eventually.of_forall fun z =>
      integral_nonneg fun θ =>
        mul_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 f z θ) (h0 z θ)
  · refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => ?_
    -- Monotonicity in `θ` of the inner integral.
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z hz) ?_
    · exact Filter.Eventually.of_forall fun θ =>
        mul_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 f z θ) (h0 z θ)
    · exact Filter.Eventually.of_forall fun θ =>
        mul_le_of_le_one_right (Work.Spaces.HkIntegrand_nonneg α 4 f z θ) (h1 z θ)

end Work.FTS.Apriori.Limit
