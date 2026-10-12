import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BlockBound4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BlockBound4

open scoped ContDiff

/-- `χ` is `C^∞` with compact support (`Submission.CubicChi`), so its Fréchet
derivative `fderiv ℝ χ` is continuous (chain rule: `χ` is `C¹`) and has compact
support (`HasCompactSupport.fderiv`).  A continuous compactly supported function
into a seminormed group is bounded, which gives the uniform operator-norm bound
on `fderiv ℝ χ`. -/
theorem chi_fderiv_norm_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : EuclideanSpace ℝ (Fin 3), ‖fderiv ℝ Submission.BoseGases.chi y‖ ≤ M := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.chi_hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (Submission.BoseGases.chi_contDiff.continuous_fderiv (by simp))
  exact ⟨max C 0, le_max_right _ _, fun y => le_trans (hC y) (le_max_left _ _)⟩

end Work.BlockBound4
