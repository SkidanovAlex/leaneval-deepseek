import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem rho_exp_eighth_bounds :
    (0 < Real.exp (-(1 / 8 : ℝ))) ∧ (Real.exp (-(1 / 8 : ℝ)) < 1) ∧
      ((7 / 8 : ℝ) ≤ Real.exp (-(1 / 8 : ℝ))) ∧
      ((1 / 9 : ℝ) ≤ 1 - Real.exp (-(1 / 8 : ℝ))) := by
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by norm_num), ?_, ?_⟩
  · have h := Real.add_one_le_exp (-(1 / 8 : ℝ))
    linarith
  · have h8 : (9 / 8 : ℝ) ≤ Real.exp (1 / 8) := by
      have h := Real.add_one_le_exp (1 / 8 : ℝ)
      linarith
    have hpos : (0 : ℝ) < Real.exp (1 / 8) := Real.exp_pos _
    have hupper : Real.exp (-(1 / 8 : ℝ)) ≤ 8 / 9 := by
      rw [Real.exp_neg]
      rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 8 / 9)]
      norm_num
      linarith
    linarith

end Work.BMF
