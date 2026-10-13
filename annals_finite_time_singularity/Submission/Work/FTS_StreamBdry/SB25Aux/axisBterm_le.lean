import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

theorem axisBterm_le (θ0 Vv v0 ε : ℝ) (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hε : 0 ≤ ε) (hV : |Vv - v0| ≤ ε * (Real.pi / 2 - θ0)) :
    |Real.tan θ0 * (Vv - v0)| ≤ ε * (Real.pi / 2) := by
  have hδpos : 0 < Real.pi / 2 - θ0 := by linarith [hθ0.2]
  have hδlt : Real.pi / 2 - θ0 < Real.pi / 2 := by linarith [hθ0.1]
  have htanθ : 0 < Real.tan θ0 := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0.1 hθ0.2
  have htanδ : 0 < Real.tan (Real.pi / 2 - θ0) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hδpos hδlt
  -- `tan θ0 = 1 / tan (π/2 - θ0)` and `x ≤ tan x`, so `tan θ0 · (π/2 - θ0) ≤ 1 ≤ π/2`.
  have htan_eq : Real.tan θ0 = (Real.tan (Real.pi / 2 - θ0))⁻¹ := by
    have h := Real.tan_pi_div_two_sub (Real.pi / 2 - θ0)
    rwa [sub_sub_cancel] at h
  have hkey : Real.tan θ0 * (Real.pi / 2 - θ0) ≤ Real.pi / 2 := by
    rw [htan_eq, inv_mul_eq_div]
    have h1 : (Real.pi / 2 - θ0) / Real.tan (Real.pi / 2 - θ0) ≤ 1 := by
      rw [div_le_one htanδ]
      exact Real.le_tan hδpos.le hδlt
    linarith [Real.two_le_pi]
  calc |Real.tan θ0 * (Vv - v0)| = Real.tan θ0 * |Vv - v0| := by
        rw [abs_mul, abs_of_pos htanθ]
    _ ≤ Real.tan θ0 * (ε * (Real.pi / 2 - θ0)) := mul_le_mul_of_nonneg_left hV htanθ.le
    _ = ε * (Real.tan θ0 * (Real.pi / 2 - θ0)) := by ring
    _ ≤ ε * (Real.pi / 2) := mul_le_mul_of_nonneg_left hkey hε

end Work.FTS_StreamBdry.SB25Aux
