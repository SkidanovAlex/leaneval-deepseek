/-
# The bound `C0Ih ≤ 729`

`C0Ih = ∫_{Iθ} h'(θ)² dθ` with `h = C0h`, `h' = C0g` (see
`Submission.Work.Coercivity.C0Defs` and `Submission.Work.Coercivity.C0h_deriv`) and
`Iθ = [0,π/2]`.  This file proves the crude numerical bound `C0Ih ≤ 729` needed by the
coercivity estimate `|C0 f|² ≤ 32 Ef f` (`C0_sq_le`).

The argument is elementary:

* write `u = cos²θ ∈ [0,1]`.  Then `sin²θ = 1 - u` and
  `2 cos²θ - 3 sin²θ = 5 cos²θ - 3`, so
  `C0g θ² = 324 · (1-u)u²(5u-3)²`;
* `(1-u)u² ≤ 4/27` for `u ∈ [0,1]`, because `27u²(1-u) ≤ 4` is equivalent to
  `(3u-2)²(3u+1) ≥ 0`;
* `(5u-3)² ≤ 9` for `u ∈ [0,1]`;
* hence `C0g θ² ≤ 324 · (4/27) · 9 = 432` for every `θ`, and
  `C0Ih ≤ 432 · vol(Iθ) = 432 · π/2 = 216π < 729` (using `π < 3.15`).

(The true value is `∫_{Iθ} C0g² = 1539π/128 ≈ 37.8`, so `729` is a very comfortable
bound; the point is only that the constant is explicit and elementary.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Coercivity.C0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set
open scoped Real Topology

set_option autoImplicit false

/-- Pointwise bound for the angular density `h' = C0g`:
`C0g(θ)² ≤ 432` for every `θ`.  Writing `u = cos²θ ∈ [0,1]` one has
`C0g(θ)² = 324 (1-u)u²(5u-3)²`, and `(1-u)u² ≤ 4/27`, `(5u-3)² ≤ 9`. -/
private lemma C0g_sq_le (θ : ℝ) : (C0g θ) ^ 2 ≤ 432 := by
  have hc0 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hc1 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  -- the purely polynomial bound at `u = cos²θ`
  have hpoly : Real.sin θ ^ 2 * (Real.cos θ ^ 2) ^ 2 * (5 * Real.cos θ ^ 2 - 3) ^ 2 ≤ 4 / 3 := by
    rw [hs]
    have hA : (1 - Real.cos θ ^ 2) * (Real.cos θ ^ 2) ^ 2 ≤ 4 / 27 := by
      have h3 : 0 ≤ (3 * Real.cos θ ^ 2 - 2) ^ 2 * (3 * Real.cos θ ^ 2 + 1) := by
        nlinarith [sq_nonneg (3 * Real.cos θ ^ 2 - 2)]
      nlinarith [h3]
    have hB : (5 * Real.cos θ ^ 2 - 3) ^ 2 ≤ 9 := by
      nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
    calc (1 - Real.cos θ ^ 2) * (Real.cos θ ^ 2) ^ 2 * (5 * Real.cos θ ^ 2 - 3) ^ 2
        = ((1 - Real.cos θ ^ 2) * (Real.cos θ ^ 2) ^ 2) * ((5 * Real.cos θ ^ 2 - 3) ^ 2) := by
          ring
      _ ≤ (4 / 27) * 9 := mul_le_mul hA hB (by positivity) (by positivity)
      _ = 4 / 3 := by norm_num
  -- rewrite `C0g` in terms of `u = cos²θ`
  have hC0g : C0g θ = 18 * Real.sin θ * Real.cos θ ^ 2 * (5 * Real.cos θ ^ 2 - 3) := by
    simp only [C0g]
    rw [hs]; ring
  rw [hC0g]
  have key : (18 * Real.sin θ * Real.cos θ ^ 2 * (5 * Real.cos θ ^ 2 - 3)) ^ 2
      = 324 * (Real.sin θ ^ 2 * (Real.cos θ ^ 2) ^ 2 * (5 * Real.cos θ ^ 2 - 3) ^ 2) := by
    ring
  rw [key]
  nlinarith [hpoly]

/-- `C0Ih = ∫_{Iθ} h'(θ)² dθ ≤ 729`.  Since `Iθ = [0,π/2]` has length `π/2` and
`C0g² ≤ 432` pointwise, `C0Ih ≤ 432 · π/2 = 216π < 729`. -/
theorem C0Ih_le : C0Ih ≤ 729 := by
  rw [C0Ih]
  have h0 : (0 : ℝ) ≤ π / 2 := by positivity
  rw [Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h0]
  have hcont : Continuous fun θ : ℝ => (C0g θ) ^ 2 := by
    simp only [C0g]; fun_prop
  calc ∫ θ in (0 : ℝ)..(π / 2), (C0g θ) ^ 2
      ≤ ∫ θ in (0 : ℝ)..(π / 2), (432 : ℝ) := by
        apply intervalIntegral.integral_mono h0
        · exact hcont.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · exact C0g_sq_le
    _ = 432 * (π / 2) := by
        rw [intervalIntegral.integral_const]; ring
    _ ≤ 729 := by nlinarith [Real.pi_lt_d2]

end Work.Coercivity
