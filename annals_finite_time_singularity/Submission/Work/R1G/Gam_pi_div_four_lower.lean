import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
set_option linter.unusedVariables false

namespace Work.R1G

/-- At `θ = π/4` the base `sin θ · cos²θ` of `Γ` equals `√2 / 4 = 2^{-3/2}`. -/
private lemma sin_mul_cos_sq_pi_div_four :
    Real.sin (Real.pi / 4) * Real.cos (Real.pi / 4) ^ 2 = Real.sqrt 2 / 4 := by
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four, div_pow]
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith [h2]

/-- `Γ(π/4) = (√2/4)^{p/3}` is bounded below by `1/8` for `0 < p ≤ 1`:
the base `√2/4 ∈ (0,1)` makes the exponential decreasing in the exponent, and
`(√2/4)^{1/3} = 2^{-1/2} ≥ 1/8`. -/
theorem Gam_pi_div_four_lower {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    1 / 8 ≤ Work.Spaces.Gam p (Real.pi / 4) := by
  have hbase := sin_mul_cos_sq_pi_div_four
  have hx : Work.Spaces.Gam p (Real.pi / 4) = (Real.sqrt 2 / 4) ^ (p / 3) := by
    rw [Work.Spaces.Gam, hbase]
  rw [hx]
  have hx0 : 0 < Real.sqrt 2 / 4 := by positivity
  have hx1 : Real.sqrt 2 / 4 ≤ 1 := by
    have h : Real.sqrt 2 ≤ 4 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_nonneg 2, this]
    linarith
  have hexp : p / 3 ≤ (1 : ℝ) / 3 := by linarith
  have hmono : (Real.sqrt 2 / 4) ^ ((1 : ℝ) / 3) ≤ (Real.sqrt 2 / 4) ^ (p / 3) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hexp
  have hge : 1 / 8 ≤ (Real.sqrt 2 / 4) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_le_rpow_iff (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (Real.rpow_nonneg (le_of_lt hx0) _) (by norm_num : (0 : ℝ) < 3)]
    rw [← Real.rpow_mul (le_of_lt hx0) ((1 : ℝ) / 3) 3]
    norm_num
    have h1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    linarith
  linarith [hge, hmono, hp]

end Work.R1G
