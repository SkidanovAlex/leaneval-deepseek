import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

theorem cos_pi_pow96_le_exp_neg192 (s : ℝ) (hs : |s| ≤ 1 / 2) :
    Real.cos (Real.pi * s) ^ 96 ≤ Real.exp (-(192 : ℝ) * s ^ 2) := by
  -- `s ^ 2 ≤ 1 / 4`
  have hs2 : s ^ 2 ≤ 1 / 4 := by
    have h : |s| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg s) hs 2
    rw [sq_abs] at h
    norm_num at h
    exact h
  -- `|π * s| ≤ π / 2`
  have hpi_s : |Real.pi * s| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, hs]
  -- Jordan-type bound: `cos (π s) ≤ 1 - 2 s ^ 2`
  have hcos_le : Real.cos (Real.pi * s) ≤ 1 - 2 * s ^ 2 := by
    have h := Real.cos_le_one_sub_mul_cos_sq (x := Real.pi * s) (by linarith [hpi_s, Real.pi_pos])
    have heq : 2 / Real.pi ^ 2 * (Real.pi * s) ^ 2 = 2 * s ^ 2 := by field_simp
    rwa [heq] at h
  -- nonnegativity of the base on the range
  have hcos_nonneg : 0 ≤ Real.cos (Real.pi * s) := by
    refine Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_
    · linarith [(abs_le.mp hpi_s).1]
    · linarith [(abs_le.mp hpi_s).2]
  have h1 : Real.cos (Real.pi * s) ^ 96 ≤ (1 - 2 * s ^ 2) ^ 96 :=
    pow_le_pow_left₀ hcos_nonneg hcos_le 96
  -- Bernoulli-type bound: `(1 - 2 s ^ 2) ^ 96 ≤ exp (-(192 s ^ 2))`
  have h2 : (1 - 2 * s ^ 2) ^ 96 ≤ Real.exp (-(192 : ℝ) * s ^ 2) := by
    have h96 : (192 : ℝ) * s ^ 2 ≤ 96 := by nlinarith [hs2]
    have h := Real.one_sub_div_pow_le_exp_neg (n := 96) (t := 192 * s ^ 2) h96
    convert h using 1
    · push_cast; ring
    · congr 1; ring
  exact le_trans h1 h2

end Work.BoseFixB1S
