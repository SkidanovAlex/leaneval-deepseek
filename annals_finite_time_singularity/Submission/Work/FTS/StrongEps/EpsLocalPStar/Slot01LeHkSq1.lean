import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

/-- The `(0,1)`-slot of the `ℋ¹`-integrand: `(D_θ f · W)²` is one of the summands of
`HkIntegrand α 1 f` (namely the mixed term `i = 1`, `j = 0`), so the `θ`-integral of the
slot is bounded by the `θ`-integral of the integrand, and hence by `HkSq α 1 f`. -/
theorem Slot01LeHkSq1 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 1 f := by
  have hprod : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed 0 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm 0 1
      (by norm_num) (by norm_num)
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
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 1 f z θ 1 0 (by norm_num) (by norm_num)

end Work.FTS.StrongEps.EpsLocalPStar
