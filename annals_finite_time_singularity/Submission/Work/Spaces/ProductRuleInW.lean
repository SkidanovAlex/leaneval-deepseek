import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
namespace Work.Spaces
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary nonnegativity facts -/

/-- The `𝒲^{l,∞}`-norm is nonnegative whenever it is honest. -/
theorem WlInf_nonneg (α : ℝ) (l : ℕ) (h : ℝ → ℝ → ℝ) (hmem : WlInfMem α l h) :
    0 ≤ WlInf α l h := by
  rw [WlInf]
  exact add_nonneg (wlZSum_nonneg α l h hmem) (wlThSum_nonneg α l h hmem)

/-- The angular factor `Φ_i(θ) = 1` for `i = 0`, `= (α + sin 2θ) sin(2θ)^{α/5}` for `i ≥ 1`
is nonnegative. -/
theorem psi_nonneg (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) (i : ℕ) :
    0 ≤ (if i = 0 then (1 : ℝ) else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  by_cases h : i = 0
  · rw [if_pos h]; norm_num
  · rw [if_neg h]
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)

/-! ## The product rule -/


end Work.Spaces
