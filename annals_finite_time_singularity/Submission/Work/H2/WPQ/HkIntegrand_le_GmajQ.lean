import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.WPQ.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.WPQ

/-- `GmajQ α g` is the `ℋ⁴`-integrand of `g` plus a nonnegative angular-Hardy correction
term, so it dominates `HkIntegrand α 4 g` pointwise at every angle of the domain. -/
theorem HkIntegrand_le_GmajQ {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 g z θ ≤ Work.FTS.H2.WPQ.GmajQ α g z θ := by
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  rw [Work.FTS.H2.WPQ.GmajQ]
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (inv_nonneg.mpr hγ1.le)
    (Work.FTS.H2.WPQ.sum_Aang_nonneg α g z)) (Work.FTS.H2.WPQ.theta_factor_nonneg hθ))

end Work.H2.WPQ
