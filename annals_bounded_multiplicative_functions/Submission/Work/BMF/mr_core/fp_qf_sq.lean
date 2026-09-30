import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BMF.mr_core

/-- The squared `qf` factor
`(exp (x^(1/8)/ε * (384 log x)))^2` is eventually dominated by `exp x`.

Indeed the square is `exp (768/ε * x^(1/8) * log x)`, and for every constant `C > 0`
one has `C * x^(1/8) * log x ≤ x` for all sufficiently large `x`, because
`log = o(x^(7/8))` at `+∞` (`isLittleO_log_rpow_atTop`). -/
theorem fp_qf_sq (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ L : ℝ, ∀ x : ℝ, L ≤ x →
      (Real.exp (x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x))) ^ 2 ≤ Real.exp x := by
  -- `log x = o(x^(7/8))`, hence eventually `log x ≤ (ε/768) * x^(7/8)`.
  have hlit : Real.log =o[Filter.atTop] (fun x : ℝ => x ^ ((7 : ℝ) / 8)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hε' : 0 < ε / 768 := by positivity
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ≤ (ε / 768) * x ^ ((7 : ℝ) / 8) := by
    filter_upwards [hlit.def hε', Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.log_nonneg hx1),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)] at hx
    exact hx
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max L₀ 1, fun x hx => ?_⟩
  have hxL : L₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
  have hlog : Real.log x ≤ (ε / 768) * x ^ ((7 : ℝ) / 8) := hL₀ x hxL
  have hx18 : 0 ≤ x ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hxpos.le _
  -- Multiply by `x^(1/8) ≥ 0` and use `x^(1/8) * x^(7/8) = x`.
  have hstep : x ^ ((1 : ℝ) / 8) * Real.log x ≤ (ε / 768) * x := by
    calc x ^ ((1 : ℝ) / 8) * Real.log x
        ≤ x ^ ((1 : ℝ) / 8) * ((ε / 768) * x ^ ((7 : ℝ) / 8)) :=
          mul_le_mul_of_nonneg_left hlog hx18
      _ = (ε / 768) * (x ^ ((1 : ℝ) / 8) * x ^ ((7 : ℝ) / 8)) := by ring
      _ = (ε / 768) * x ^ ((1 : ℝ) / 8 + (7 : ℝ) / 8) := by rw [Real.rpow_add hxpos]
      _ = (ε / 768) * x := by
            rw [show (1 : ℝ) / 8 + (7 : ℝ) / 8 = 1 by norm_num, Real.rpow_one]
  -- Multiply by `768/ε > 0`.
  have hkey : 768 / ε * (x ^ ((1 : ℝ) / 8) * Real.log x) ≤ x := by
    calc 768 / ε * (x ^ ((1 : ℝ) / 8) * Real.log x)
        ≤ 768 / ε * ((ε / 768) * x) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = x := by field_simp
  -- Identify the exponent and compare the exponentials.
  rw [← Real.exp_nat_mul]
  rw [show ((2 : ℕ) : ℝ) * (x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x))
      = 768 / ε * (x ^ ((1 : ℝ) / 8) * Real.log x) from by ring]
  exact Real.exp_le_exp.mpr hkey

end Work.BMF.mr_core
