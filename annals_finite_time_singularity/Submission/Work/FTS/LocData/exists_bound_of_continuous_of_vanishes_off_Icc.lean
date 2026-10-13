import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

theorem exists_bound_of_continuous_of_vanishes_off_Icc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Continuous g) (hvan : ∀ z, z ∉ Set.Icc a b → g z = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ, |g z| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ Set.Icc a b
  · have h := hC z hz
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · rw [hvan z hz, abs_zero]
    exact le_max_right _ _

end Work.FTS.LocData
