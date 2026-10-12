import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

theorem sqrt_LM_eq {μ L M X : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hX : 0 < X)
    (hML : M = X ^ (337 / 4 : ℝ) * (μ * L ^ 3)) :
    Real.sqrt (L ^ 3 * M) = X ^ (337 / 8 : ℝ) * Real.sqrt μ * L ^ 3 := by
  rw [hML]
  have _ : (0 : ℝ) < μ := hμ
  have hL3 : (0 : ℝ) < L ^ 3 := by positivity
  have hX4 : (0 : ℝ) < X ^ (337 / 4 : ℝ) := Real.rpow_pos_of_pos hX _
  have hsqrtX : Real.sqrt (X ^ (337 / 4 : ℝ)) = X ^ (337 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX.le]
    norm_num
  have harg : L ^ 3 * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3))
      = (L ^ 3) ^ 2 * (X ^ (337 / 4 : ℝ) * μ) := by ring
  rw [harg, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (L ^ 3) ^ 2),
    Real.sqrt_sq hL3.le, Real.sqrt_mul hX4.le, hsqrtX]
  ring

end Work.BoseFixR
