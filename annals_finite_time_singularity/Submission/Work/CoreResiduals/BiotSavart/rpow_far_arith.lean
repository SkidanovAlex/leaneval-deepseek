import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.CoreResiduals.BiotSavart.rpow_sq_le_exp_small

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- Arithmetic residual estimate used when both the singular point and the evaluation point are
far from the origin: for `0 < α < 1` and `0 < d ≤ s`,
`1024 d ^ 2 s ^ (-4) + 4 d s ^ (-3) ≤ 1028 d ^ α s ^ (-2 - α)`.

Writing `u = d / s ∈ (0,1]` and `d = u s`, the three terms become `u ^ 2 s ^ (-2)`, `u s ^ (-2)`
and `d ^ α s ^ (-2 - α) = u ^ α s ^ (-2)`, so the claim reduces (after cancelling the common
positive factor `s ^ (-2)`) to the elementary comparison `rpow_sq_le_exp_small`. -/
theorem rpow_far_arith {α d s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hd : 0 < d) (hs : 0 < s)
    (hds : d ≤ s) :
    1024 * d ^ (2 : ℝ) * s ^ (-4 : ℝ) + 4 * d * s ^ (-3 : ℝ) ≤ 1028 * d ^ α * s ^ (-2 - α) := by
  set u : ℝ := d / s with hu
  have hu_pos : 0 < u := by rw [hu]; exact div_pos hd hs
  have hu_le : u ≤ 1 := by rw [hu]; exact (div_le_one hs).mpr hds
  have hd_eq : d = u * s := by rw [hu, div_mul_cancel₀ d hs.ne']
  have hkey : 1024 * u ^ (2 : ℝ) + 4 * u ≤ 1028 * u ^ α :=
    rpow_sq_le_exp_small hu_pos hu_le hα hα1
  have hs2pos : (0 : ℝ) < s ^ (-2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hmult : (1024 * u ^ (2 : ℝ) + 4 * u) * s ^ (-2 : ℝ) ≤ 1028 * u ^ α * s ^ (-2 : ℝ) :=
    mul_le_mul_of_nonneg_right hkey hs2pos.le
  have h1 : (u * s) ^ (2 : ℝ) = u ^ (2 : ℝ) * s ^ (2 : ℝ) := Real.mul_rpow hu_pos.le hs.le
  have h2 : (u * s) ^ α = u ^ α * s ^ α := Real.mul_rpow hu_pos.le hs.le (z := α)
  have hs2 : s ^ (2 : ℝ) * s ^ (-4 : ℝ) = s ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hs (2 : ℝ) (-4)]
    norm_num
  have hs3 : s * s ^ (-3 : ℝ) = s ^ (-2 : ℝ) := by
    calc s * s ^ (-3 : ℝ) = s ^ (1 : ℝ) * s ^ (-3 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ ((1 : ℝ) + (-3)) := (Real.rpow_add hs 1 (-3)).symm
      _ = s ^ (-2 : ℝ) := by rw [show (1 : ℝ) + (-3) = -2 by norm_num]
  have hs4 : s ^ α * s ^ (-2 - α) = s ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hs α (-2 - α), show α + (-2 - α) = (-2 : ℝ) by ring]
  have hL : 1024 * (u ^ (2 : ℝ) * s ^ (2 : ℝ)) * s ^ (-4 : ℝ) + 4 * (u * s) * s ^ (-3 : ℝ)
      = (1024 * u ^ (2 : ℝ) + 4 * u) * s ^ (-2 : ℝ) := by
    rw [show (1024 : ℝ) * (u ^ (2 : ℝ) * s ^ (2 : ℝ)) * s ^ (-4 : ℝ)
          = 1024 * u ^ (2 : ℝ) * (s ^ (2 : ℝ) * s ^ (-4 : ℝ)) by ring,
        show (4 : ℝ) * (u * s) * s ^ (-3 : ℝ) = 4 * u * (s * s ^ (-3 : ℝ)) by ring,
        hs2, hs3]
    ring
  have hR : 1028 * u ^ α * s ^ (-2 : ℝ) = 1028 * (u ^ α * s ^ α) * s ^ (-2 - α) := by
    rw [← hs4]
    ring
  rw [hd_eq, h1, h2, hL, ← hR]
  exact hmult

end Work.CoreResiduals.BiotSavart
