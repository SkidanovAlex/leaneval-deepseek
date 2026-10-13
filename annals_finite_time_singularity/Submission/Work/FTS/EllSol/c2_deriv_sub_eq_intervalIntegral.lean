import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllSol.Base

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllSol

/-- The fundamental theorem of calculus for a `C²` function on an open interval: the
increment of the first derivative is the integral of the second derivative. -/
theorem c2_deriv_sub_eq_intervalIntegral {h : ℝ → ℝ} {ε a b : ℝ}
    (hC2 : ContDiffOn ℝ 2 h (Set.Ioo 0 ε)) (ha : 0 < a) (hab : a ≤ b) (hb : b < ε) :
    deriv h b - deriv h a = ∫ x in a..b, deriv (deriv h) x := by
  have hsub : Icc a b ⊆ Ioo 0 ε := fun x hx =>
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hcont : ContinuousOn (deriv h) (Icc a b) := (c2_continuousOn_deriv hC2).mono hsub
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt (deriv h) (deriv (deriv h) x) x :=
    fun x hx => c2_hasDerivAt_deriv hC2 (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv
    (c2_intervalIntegrable_deriv_deriv hC2 ha hab hb)).symm

end Work.FTS.EllSol
