import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Regime

open Work.BoseBox

/-- The whole content: dividing by `μ * A > 0`, the right-hand side is
`μ * A * fsXp (μ A³) (-(45/2))`, which is `≥ μ * A` since `μ A³ ≤ 1`. -/
theorem muA_le_muA_ell_cube_KB3 {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht : μ * A ^ 3 ≤ 1) : μ * A ≤ μ ^ 2 * A * sideAt μ A ^ 3 * (paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by
  have ht0 : (0 : ℝ) < μ * A ^ 3 := by positivity
  have hμA : (0 : ℝ) ≤ μ * A := by positivity
  have h1 : 1 ≤ fsXp (μ * A ^ 3) (-(45 / 2)) := one_le_fsXp_of ht0 ht (by norm_num)
  calc μ * A = μ * A * 1 := by ring
    _ ≤ μ * A * fsXp (μ * A ^ 3) (-(45 / 2)) := mul_le_mul_of_nonneg_left h1 hμA
    _ = μ * A * (μ * sideAt μ A ^ 3 * (paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ)) := by
          rw [mu_ell_cube_KB3_half_eq hA hμ]
    _ = μ ^ 2 * A * sideAt μ A ^ 3 * (paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by ring

end Work.BoseFixB1.Regime
