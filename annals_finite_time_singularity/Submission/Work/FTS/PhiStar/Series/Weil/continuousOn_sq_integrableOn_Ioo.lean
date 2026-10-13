import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Weil

/-- The square of a function continuous on `[a, b]` is integrable on the open interval
`(a, b)`.  (The hypothesis `a ≤ b` is not needed for the argument: `[a, b]` is compact
in either case, and the empty interval case is trivial.) -/
theorem continuousOn_sq_integrableOn_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => f θ ^ 2) (Set.Ioo a b) := by
  -- `f ^ 2` is continuous on the compact interval `[a, b]`, hence integrable there;
  -- restricting to the smaller set `(a, b) ⊆ [a, b]` preserves integrability.
  have _ : a ≤ b := hab
  exact (hf.pow 2).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self

end Work.FTS.PhiStar.Series.Weil
