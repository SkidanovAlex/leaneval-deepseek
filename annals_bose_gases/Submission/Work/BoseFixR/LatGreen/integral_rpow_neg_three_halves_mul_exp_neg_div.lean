import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Submission.Commons.Analysis.Integral.integral_heat_coulomb_three
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open MeasureTheory Real Set

/-- The Green's-function tail integral of the lattice/continuum convolution localisation:
`∫₀^∞ t ^ (-3/2) exp (-(a/t)) dt = √(π/a)` for `a > 0`.

This is the Euler/Gamma substitution `u = a/t` applied to `∫₀^∞ u ^ (-1/2) e ^ (-u) du = Γ(1/2)`,
formalised via `Commons.Analysis.Integral.integral_rpow_exp_neg_div_Ioi` — the substitution
`t ↦ 1/t` on `(0,∞)` — combined with `Γ(1/2) = √π`. -/
theorem integral_rpow_neg_three_halves_mul_exp_neg_div {a : ℝ} (ha : 0 < a) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t))
      = Real.sqrt (Real.pi / a) := by
  have h := Commons.Analysis.Integral.integral_rpow_exp_neg_div_Ioi
    (s := -(1 / 2 : ℝ)) (c := a) ha (by norm_num)
  have harg : (-(3 / 2 : ℝ)) = -(1 / 2 : ℝ) - 1 := by norm_num
  rw [harg, h]
  simp only [neg_neg]
  rw [Real.Gamma_one_half_eq]
  rw [Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow, Real.sqrt_div Real.pi_pos.le a, div_eq_inv_mul]

end Work.BoseFixR.LatGreen
