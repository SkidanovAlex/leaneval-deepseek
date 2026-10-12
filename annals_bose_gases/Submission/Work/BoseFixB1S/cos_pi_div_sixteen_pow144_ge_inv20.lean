import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB1S.oneD_pow96_integral_le_conv48
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- The rational-power core: `(49/50)^144 ≥ 1/20`.  Since `1/20 = 0.05` and
`(49/50)^144 ≈ 0.0545`, this is a (tight but genuine) numerical fact. -/
lemma pow_49_div_50_pow144_ge_inv20 : (1 / 20 : ℝ) ≤ (49 / 50 : ℝ) ^ 144 := by
  norm_num

/-- `cos (π/16) ≥ 49/50`, from the Taylor bound `cos x ≥ 1 - x²/2` at `x = π/16`
and the crude estimate `π < 16/5`, which gives `(π/16)²/2 < 1/50` exactly. -/
lemma cos_pi_div_sixteen_ge_49_div_50 : (49 / 50 : ℝ) ≤ Real.cos (Real.pi / 16) := by
  have hpi : Real.pi < 16 / 5 := by linarith [Real.pi_lt_d2]
  have hcos_ge : 1 - (Real.pi / 16) ^ 2 / 2 ≤ Real.cos (Real.pi / 16) :=
    Real.one_sub_sq_div_two_le_cos
  have hle : (49 / 50 : ℝ) ≤ 1 - (Real.pi / 16) ^ 2 / 2 := by
    have h : (Real.pi / 16) ^ 2 / 2 < 1 / 50 := by
      have h2 : Real.pi ^ 2 < (16 / 5 : ℝ) ^ 2 := by nlinarith [Real.pi_pos, hpi]
      have heq : (Real.pi / 16) ^ 2 / 2 = Real.pi ^ 2 / 512 := by ring
      rw [heq]; nlinarith
    linarith
  linarith

theorem cos_pi_div_sixteen_pow144_ge_inv20 : (1 / 20 : ℝ) ≤ Real.cos (Real.pi / 16) ^ 144 := by
  have h49 : (0 : ℝ) ≤ 49 / 50 := by norm_num
  calc (1 / 20 : ℝ) ≤ (49 / 50 : ℝ) ^ 144 := pow_49_div_50_pow144_ge_inv20
    _ ≤ Real.cos (Real.pi / 16) ^ 144 :=
        pow_le_pow_left₀ h49 cos_pi_div_sixteen_ge_49_div_50 144

end Work.BoseFixB1S
