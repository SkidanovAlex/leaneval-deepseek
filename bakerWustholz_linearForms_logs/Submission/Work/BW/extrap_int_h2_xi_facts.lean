import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_xi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Elementary facts about `ξ = pxi r = 1 - 0.536/r` and the exponents occurring in
`extrap_int_h2` (all pure algebra/numerics; `num_xi` gives `1.07 ≤ 2ξ^r`, `ξ > 0`, `ξ ≤ 1`).
Routes: `pxi r ^ (-((r*J:ℕ):ℤ)) * pxi r ^ (r*J) = 1` by `zpow_neg` + `zpow_natCast` +
`inv_mul_cancel₀` (`pxi r ≠ 0`); `pxi r ^ (-((r*J:ℕ):ℤ)) / 2^J = ((2 * pxi r ^ r)⁻¹)^J` by
`div_eq_mul_inv`, `mul_pow`, `inv_pow`, `zpow_neg`, `zpow_natCast`, `mul_pow` (`(ξ^r)^J = ξ^(r*J)`);
`1 ≤ ξ^{-(rJ)}` by `one_le_inv₀`-style from `0 < ξ^(rJ) ≤ 1`; `2^j ≤ 2^(r-2)` from `hj` by
`pow_le_pow_right₀`. -/
theorem extrap_int_h2_xi_facts {r : ℕ} (hr : 2 ≤ r) (J j : ℕ) (hj : j + 2 ≤ r) :
    0 < pxi r ∧ pxi r ≤ 1 ∧
    (1 : ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) ∧
    pxi r ^ (-((r * J : ℕ) : ℤ)) * pxi r ^ (r * J) = 1 ∧
    pxi r ^ j * pxi r ^ (r * J) = pxi r ^ (j + r * J) ∧
    pxi r ^ (-((r * J : ℕ) : ℤ)) / (2 : ℝ) ^ J = ((2 * pxi r ^ r)⁻¹) ^ J ∧
    (0 : ℝ) ≤ pxi r ^ j ∧ pxi r ^ j ≤ 1 ∧
    (0 : ℝ) < pxi r ^ (r * J) ∧ pxi r ^ (r * J) ≤ 1 ∧
    (1 : ℝ) ≤ (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (r - 2) ∧
    1.07 ≤ 2 * pxi r ^ r ∧ ((2 * pxi r ^ r)⁻¹) ^ J ≤ 1 := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have h2r : (2:ℝ) ≤ r := by exact_mod_cast hr
  -- `ξ = 1 - 0.536/r ∈ (0,1]` for `r ≥ 2`.
  have hxipos : 0 < pxi r := by
    rw [pxi]
    have : (0.536:ℝ)/r < 1 := by rw [div_lt_one hr0]; linarith
    linarith
  have hxile1 : pxi r ≤ 1 := by
    rw [pxi]
    have : (0:ℝ) ≤ (0.536:ℝ)/r := by positivity
    linarith
  have hxine : pxi r ≠ 0 := ne_of_gt hxipos
  have hxi0 : 0 ≤ pxi r := le_of_lt hxipos
  -- BW's `b = 2ξ^r ≥ 1.07` (from `num_xi`).
  have hb : 1.07 ≤ 2 * pxi r ^ r := (num_xi hr).2.2.2.2
  -- `1 ≤ ξ^{-(rJ)}` since `0 < ξ^{rJ} ≤ 1`.
  have h1 : (1:ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact (one_le_inv₀ (pow_pos hxipos (r*J))).mpr (pow_le_one₀ hxi0 hxile1)
  -- `ξ^{-(rJ)} * ξ^{rJ} = 1`.
  have h2 : pxi r ^ (-((r * J : ℕ) : ℤ)) * pxi r ^ (r * J) = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero (r*J) hxine)]
  refine ⟨hxipos, hxile1, h1, h2, (pow_add _ _ _).symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb, ?_⟩
  -- `ξ^{-(rJ)} / 2^J = ((2ξ^r)⁻¹)^J`.
  · rw [zpow_neg, zpow_natCast, div_eq_mul_inv, inv_pow, mul_pow, mul_inv_rev, pow_mul]
  · exact pow_nonneg hxi0 j
  · exact pow_le_one₀ hxi0 hxile1
  · exact pow_pos hxipos (r*J)
  · exact pow_le_one₀ hxi0 hxile1
  · exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  · exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
  -- `((2ξ^r)⁻¹)^J ≤ 1` since `1 ≤ 2ξ^r`.
  · apply pow_le_one₀
    · exact inv_nonneg.mpr (by positivity)
    · exact inv_le_one_of_one_le₀ (by linarith [hb])

end Work.BW
