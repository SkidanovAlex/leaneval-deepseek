import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real
open MeasureTheory Set

/-!
# Definitions for the second `cos`-weight tail estimate

The target estimate (`Work.FTS_EllLimOK.PkgJets.cosTailB`) is
`∫_0^T sin(2s)^{-η}/cos(s)^4 ds ≤ C (π/2 - T)^{-(3+η)}`, `η = 99/100`.

The proof splits at `π/4`; on `(0, π/4]` the integrand is dominated by a multiple of
`s^{-η}` (`ctA`), and in the reflected variable `w = π/2 - s` (also on `(0, π/4]`) by a
multiple of `w^{-(4+η)}` (`ctB`).
-/

/-- The integrand `sin(2s)^{-η}/cos(s)^4`, `η = 99/100`. -/
noncomputable def ctF (s : ℝ) : ℝ :=
  (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) / (Real.cos s) ^ (4 : ℕ)

/-- The same integrand in the reflected variable `w = π/2 - s`: `sin(2w)^{-η}/sin(w)^4`. -/
noncomputable def ctG (w : ℝ) : ℝ :=
  (Real.sin (2 * w)) ^ (-(99 / 100 : ℝ)) / (Real.sin w) ^ (4 : ℕ)

/-- Comparison function on `(0, π/4]`: `16 (4/π)^{-η} s^{-η}`. -/
noncomputable def ctA (s : ℝ) : ℝ :=
  16 * (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * s ^ (-(99 / 100 : ℝ))

/-- Comparison function on `(0, π/4]` in the variable `w = π/2 - s`:
`(4/π)^{-η} (π/2)^4 w^{-(4+η)}`. -/
noncomputable def ctB (w : ℝ) : ℝ :=
  (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * (Real.pi / 2) ^ (4 : ℕ)
    * w ^ (-(4 + 99 / 100 : ℝ))

/-- Reflection identity: the integrand in the variable `π/2 - w` is `ctG w`. -/
theorem ctF_sub (w : ℝ) : ctF (Real.pi / 2 - w) = ctG w := by
  have h1 : 2 * (Real.pi / 2 - w) = Real.pi - 2 * w := by ring
  unfold ctF ctG
  rw [h1, Real.sin_pi_sub, Real.cos_pi_div_two_sub]

/-! ### Elementary numeric facts -/

theorem ct_e_pos : (0 : ℝ) < 99 / 100 := by norm_num

theorem ct_e_lt_one : (99 / 100 : ℝ) < 1 := by norm_num

theorem ct_one_sub_e : 1 - (99 / 100 : ℝ) = 1 / 100 := by norm_num

theorem ct_three_add_e : 3 + (99 / 100 : ℝ) = 399 / 100 := by norm_num

theorem ct_four_add_e_ne_one : 4 + (99 / 100 : ℝ) ≠ 1 := by norm_num

theorem ct_pi_div_two_ge_one : 1 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]

theorem ct_pi_div_four_le_one : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]

theorem ct_pi_div_four_pos : 0 < Real.pi / 4 := by linarith [Real.pi_pos]

theorem ct_pi_div_two_pos : 0 < Real.pi / 2 := by linarith [Real.pi_pos]

theorem ct_pi_div_two_lt_two : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]

theorem ct_four_div_pi_ge_one : 1 ≤ 4 / Real.pi := by
  rw [le_div_iff₀ Real.pi_pos]
  linarith [Real.pi_lt_four]

theorem ct_four_div_pi_pos : 0 < 4 / Real.pi := by positivity

/-- `(4/π)^{-η} ≤ 1`. -/
theorem ct_four_div_pi_rpow_le_one : (4 / Real.pi) ^ (-(99 / 100 : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos ct_four_div_pi_ge_one (by linarith [ct_e_pos])

/-- `(π/4)^{1-η} ≤ 1`. -/
theorem ct_pi_div_four_rpow_one_sub_le_one : (Real.pi / 4) ^ (1 - 99 / 100 : ℝ) ≤ 1 :=
  Real.rpow_le_one ct_pi_div_four_pos.le ct_pi_div_four_le_one (by linarith [ct_e_lt_one])

/-- `1 ≤ (π/4)^{-(3+η)}`. -/
theorem ct_one_le_pi_div_four_rpow : 1 ≤ (Real.pi / 4) ^ (-(3 + 99 / 100 : ℝ)) := by
  have hpos : 0 < (Real.pi / 4) ^ (3 + (99 / 100 : ℝ)) := Real.rpow_pos_of_pos ct_pi_div_four_pos _
  rw [Real.rpow_neg ct_pi_div_four_pos.le (3 + (99 / 100 : ℝ))]
  exact (one_le_inv₀ hpos).mpr
    (Real.rpow_le_one ct_pi_div_four_pos.le ct_pi_div_four_le_one (by linarith [ct_e_pos]))

/-- `(π/2)^{3+η} ≤ 16`. -/
theorem ct_pi_div_two_rpow_le_sixteen : (Real.pi / 2) ^ (3 + (99 / 100 : ℝ)) ≤ 16 := by
  have h1 : (Real.pi / 2) ^ (3 + (99 / 100 : ℝ)) ≤ (Real.pi / 2) ^ (4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ct_pi_div_two_ge_one (by norm_num)
  have h2 : (Real.pi / 2) ^ (4 : ℝ) ≤ (2 : ℝ) ^ (4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith [Real.pi_lt_four]) (by norm_num)
  have h3 : (2 : ℝ) ^ (4 : ℝ) = 16 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  linarith

/-- `1/16 ≤ (π/2)^{-(3+η)}`. -/
theorem ct_sixteenth_le_pi_div_two_rpow : (1 : ℝ) / 16 ≤ (Real.pi / 2) ^ (-(3 + 99 / 100 : ℝ)) := by
  have hpos : 0 < (Real.pi / 2) ^ (3 + (99 / 100 : ℝ)) := Real.rpow_pos_of_pos ct_pi_div_two_pos _
  rw [Real.rpow_neg ct_pi_div_two_pos.le (3 + (99 / 100 : ℝ))]
  simpa using one_div_le_one_div_of_le hpos ct_pi_div_two_rpow_le_sixteen

end Work.FTS_EllLimOK.PkgJets
