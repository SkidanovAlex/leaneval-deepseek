import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

theorem axisDterm_le (θ0 v0 : ℝ) (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |v0 * (1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3| ≤ |v0| * (Real.pi / 2 - θ0) := by
  have hcos : 0 < Real.cos θ0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0.1], hθ0.2⟩
  have hsin_nn : 0 ≤ Real.sin θ0 :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0.1.le (by linarith [hθ0.2, Real.pi_pos])
  have hsin_le1 : Real.sin θ0 ≤ 1 := Real.sin_le_one θ0
  have h1s : 0 ≤ 1 - Real.sin θ0 := by linarith
  have hY : 0 < Real.cos θ0 ^ 3 := pow_pos hcos 3
  -- `cos²θ = (1 - sin θ)(1 + sin θ)`
  have hcos2 : Real.cos θ0 ^ 2 = (1 - Real.sin θ0) * (1 + Real.sin θ0) := by
    have h := Real.sin_sq_add_cos_sq θ0
    nlinarith [h]
  -- `(1 - sin θ)² ≤ cos⁴θ`
  have hsq : (1 - Real.sin θ0) ^ 2 ≤ Real.cos θ0 ^ 4 := by
    have hle : 1 - Real.sin θ0 ≤ Real.cos θ0 ^ 2 := by
      rw [hcos2]; nlinarith
    have := pow_le_pow_left₀ h1s hle 2
    calc (1 - Real.sin θ0) ^ 2 ≤ (Real.cos θ0 ^ 2) ^ 2 := this
      _ = Real.cos θ0 ^ 4 := by ring
  -- hence `(1 - sin θ)² / cos³θ ≤ cos θ`
  have key1 : (1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3 ≤ Real.cos θ0 := by
    rw [div_le_iff₀ hY]
    nlinarith [hsq]
  -- and `cos θ = sin (π/2 - θ) ≤ π/2 - θ`
  have key2 : Real.cos θ0 ≤ Real.pi / 2 - θ0 := by
    rw [← Real.sin_pi_div_two_sub θ0]
    exact Real.sin_le (by linarith [hθ0.2])
  have key := le_trans key1 key2
  have hXY : 0 ≤ (1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3 := div_nonneg (sq_nonneg _) hY.le
  have habs : |v0 * (1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3|
      = |v0| * ((1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3) := by
    rw [mul_div_assoc, abs_mul, abs_of_nonneg hXY]
  rw [habs]
  exact mul_le_mul_of_nonneg_left key (abs_nonneg v0)

end Work.FTS_StreamBdry.SB25Aux
