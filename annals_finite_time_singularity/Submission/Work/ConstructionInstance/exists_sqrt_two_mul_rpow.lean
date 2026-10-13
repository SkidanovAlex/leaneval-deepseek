import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem exists_sqrt_two_mul_rpow {p s : ℝ} (hp : 0 < p) (hs : 0 < s) :
    ∃ t : ℝ, 0 < t ∧ (Real.sqrt 2 * t) ^ p = s := by
  refine ⟨s ^ (1 / p) / Real.sqrt 2, ?_, ?_⟩
  · positivity
  · have hbase : Real.sqrt 2 * (s ^ (1 / p) / Real.sqrt 2) = s ^ (1 / p) := by
      field_simp
    rw [hbase, ← Real.rpow_mul (le_of_lt hs) (1 / p) p, one_div,
      inv_mul_cancel₀ (ne_of_gt hp), Real.rpow_one]

end Work.ConstructionInstance
