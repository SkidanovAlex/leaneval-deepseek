import Mathlib
import Submission.Work.BW.num_xi
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For `r ≥ 2` and any `J`, the negative-power ratio
`8 · ξ^{-rJ} / 2^{J+1} ≤ 4`, where `ξ = pxi r = 1 - 0.536/r ∈ (0,1)`.

Route: `ξ^{-r} ≤ 1.87 ≤ 2` (`num_xi`), hence `ξ^{-rJ} = (ξ^{-r})^J ≤ 2^J`;
then `8 · ξ^{-rJ} / 2^{J+1} ≤ 8 · 2^J / (2^J · 2) = 4`. -/
theorem pxi_ratio_eight_le {r : ℕ} (hr : 2 ≤ r) (J : ℕ) :
    8 * pxi r ^ (-((r * J : ℕ) : ℤ)) / 2 ^ (J + 1) ≤ 4 := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hxipos : 0 < pxi r := by
    rw [pxi]
    have h : (0.536 : ℝ) / (r : ℝ) < 1 := by rw [div_lt_one hr0]; linarith
    linarith
  -- `ξ^{-rJ} ≤ 2^J`, from `ξ^{-r} ≤ 1.87 ≤ 2`
  have hpow : pxi r ^ (-((r * J : ℕ) : ℤ)) ≤ (2 : ℝ) ^ J := by
    have hxir : pxi r ^ (-(r : ℤ)) ≤ 1.87 := (num_xi hr).1
    have hxir_nn : (0 : ℝ) ≤ pxi r ^ (-(r : ℤ)) := zpow_nonneg hxipos.le _
    have key : pxi r ^ (-((r * J : ℕ) : ℤ)) = (pxi r ^ (-(r : ℤ))) ^ J := by
      rw [show -((r * J : ℕ) : ℤ) = -(r : ℤ) * (J : ℤ) by push_cast; ring]
      rw [zpow_mul, zpow_natCast]
    rw [key]
    calc (pxi r ^ (-(r : ℤ))) ^ J ≤ 1.87 ^ J := pow_le_pow_left₀ hxir_nn hxir J
      _ ≤ (2 : ℝ) ^ J := pow_le_pow_left₀ (by norm_num) (by norm_num) J
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (J + 1) := by positivity
  have hstep : 8 * pxi r ^ (-((r * J : ℕ) : ℤ)) / (2 : ℝ) ^ (J + 1)
      ≤ 8 * (2 : ℝ) ^ J / (2 : ℝ) ^ (J + 1) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) h2pos.le
  have heq : 8 * (2 : ℝ) ^ J / (2 : ℝ) ^ (J + 1) = 4 := by
    rw [pow_succ]
    field_simp
    norm_num
  linarith

end Work.BW
