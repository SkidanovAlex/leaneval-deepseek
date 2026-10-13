import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Arithmetic residual estimate for the "near field" part of the Biot–Savart decomposition.

For `0 < α < 1` and `0 ≤ r ≤ s ≤ 2 d` we prove
`r ^ (-2) + s ^ (-2) ≤ 1028 * d ^ α * (r ^ (-2 - α) + s ^ (-2 - α))`.

The essential content is the *single-term* bound `x ^ (-2) ≤ 1028 * d ^ α * x ^ (-2 - α)`
valid for `0 ≤ x ≤ 2 d`: rewriting `x ^ (-2) = x ^ α * x ^ (-2 - α)` (`rpow_split_sub`) and
using `x ≤ 2 d` gives
`x ^ α ≤ (2 d) ^ α = 2 ^ α * d ^ α ≤ 2 * d ^ α ≤ 1028 * d ^ α`.
Since `r ≤ s ≤ 2 d` the same estimate applies to both terms of the sum, and the two are added.
-/

namespace Work.CoreResiduals.BiotSavart

/-- Splitting a real power: for `0 ≤ x` and `c ≠ 0`, `x ^ c = x ^ β * x ^ (c - β)`.

For `x > 0` this is `Real.rpow_add`; for `x = 0` both sides vanish (the hypothesis `c ≠ 0`
rules out the exceptional case `0 ^ 0 = 1`). -/
theorem rpow_split_sub {x c β : ℝ} (hx : 0 ≤ x) (hc : c ≠ 0) :
    x ^ c = x ^ β * x ^ (c - β) := by
  rcases eq_or_lt_of_le hx with h | hxpos
  · rw [← h, Real.zero_rpow hc]
    rcases eq_or_ne β 0 with hβ | hβ
    · subst hβ
      rw [Real.rpow_zero, one_mul, sub_zero, Real.zero_rpow hc]
    · rw [Real.zero_rpow hβ, zero_mul]
  · rw [← Real.rpow_add hxpos β (c - β), add_sub_cancel]

/-- For `0 ≤ x ≤ 2 d` and `0 < α < 1` one has `x ^ α ≤ 1028 * d ^ α`. -/
theorem rpow_le_const_mul_rpow {x d α : ℝ} (hx : 0 ≤ x) (hxd : x ≤ 2 * d) (hα : 0 < α)
    (hα1 : α < 1) : x ^ α ≤ 1028 * d ^ α := by
  have hd : 0 ≤ d := by linarith
  have h1 : x ^ α ≤ (2 * d) ^ α := Real.rpow_le_rpow hx hxd hα.le
  have h2 : (2 * d) ^ α = (2 : ℝ) ^ α * d ^ α := Real.mul_rpow (by norm_num) hd
  have h3 : (2 : ℝ) ^ α ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1.le
    rwa [Real.rpow_one] at h
  have hdα : 0 ≤ d ^ α := Real.rpow_nonneg hd α
  calc x ^ α ≤ (2 * d) ^ α := h1
    _ = (2 : ℝ) ^ α * d ^ α := h2
    _ ≤ 2 * d ^ α := by nlinarith
    _ ≤ 1028 * d ^ α := by nlinarith

/-- Single-term near-field bound: for `0 ≤ x ≤ 2 d` and `0 < α < 1`,
`x ^ (-2) ≤ 1028 * d ^ α * x ^ (-2 - α)`. -/
theorem rpow_neg_two_le {x d α : ℝ} (hx : 0 ≤ x) (hxd : x ≤ 2 * d) (hα : 0 < α) (hα1 : α < 1) :
    x ^ (-2 : ℝ) ≤ 1028 * d ^ α * x ^ (-2 - α) := by
  have hxa : x ^ α ≤ 1028 * d ^ α := rpow_le_const_mul_rpow hx hxd hα hα1
  have hx1 : 0 ≤ x ^ (-2 - α) := Real.rpow_nonneg hx _
  have hmul := mul_le_mul_of_nonneg_right hxa hx1
  rw [rpow_split_sub hx (by norm_num : (-2 : ℝ) ≠ 0)]
  exact hmul

theorem rpow_near_arith {α r s d : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hrs : r ≤ s) (hsd : s ≤ 2 * d) : r ^ (-2 : ℝ) + s ^ (-2 : ℝ) ≤ 1028 * d ^ α * (r ^ (-2 - α) + s ^ (-2 - α)) := by
  have hs : 0 ≤ s := le_trans hr hrs
  have hrd : r ≤ 2 * d := le_trans hrs hsd
  have h1 : r ^ (-2 : ℝ) ≤ 1028 * d ^ α * r ^ (-2 - α) := rpow_neg_two_le hr hrd hα hα1
  have h2 : s ^ (-2 : ℝ) ≤ 1028 * d ^ α * s ^ (-2 - α) := rpow_neg_two_le hs hsd hα hα1
  calc r ^ (-2 : ℝ) + s ^ (-2 : ℝ)
      ≤ 1028 * d ^ α * r ^ (-2 - α) + 1028 * d ^ α * s ^ (-2 - α) := add_le_add h1 h2
    _ = 1028 * d ^ α * (r ^ (-2 - α) + s ^ (-2 - α)) := by ring

end Work.CoreResiduals.BiotSavart
