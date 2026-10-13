/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsRLX/ProfileSlotCompare.lean`

**The general mixed slot of the `ℋ^k`-integrand is dominated by `HkSq α k`.**

For `f` smooth on the open quadrant and honestly in `ℋ^k`, the `θ`-integral of the slot
`(D_z^j D_θ^i f · W)²` (`i ≥ 1`, `i + j ≤ k`) is `z`-integrable and its iterated integral is at
most `HkSq α k f`.

This is the general form of `Work.FTS.StrongEps.EpsLocalPStar.Slot01LeHkSq1` (the slot
`(0,1)` of `ℋ¹`): the slot is one summand of `HkIntegrand α k f` (`sq_le_HkIntegrand_mixed`),
so the only content is the comparison of the two iterated integrals, which uses the integrability
of the *whole* integrand (`HkMem α k f`) and the nonnegativity of the remaining summands.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **A mixed slot of the `ℋ^k`-integrand is dominated by `HkSq α k`.**  For `f` which is `C^∞`
on the open quadrant and honestly in `ℋ^k`, and for a slot `(j,i)` of the mixed block
(`1 ≤ i`, `i + j ≤ k`), the `θ`-integral of the slot is `z`-integrable and

  `∫_z ∫_θ (D_z^j D_θ^i f · W)² ≤ HkSq α k f`. -/
theorem slot_mixed_le_HkSq {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ Work.Spaces.HkSq α k f := by
  have hprod : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm j i hi hij
  refine ⟨?_, ?_⟩
  · simpa only [Function.uncurry, MeasureTheory.IntegrableOn]
      using hprod.integral_prod_left
  · rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
      hm.2 ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hm.1 z hz) ?_
    filter_upwards with θ
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij

end Work.FTS.StrongEps.EpsRLX
