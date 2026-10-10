import Mathlib
import Submission.Work.SilvermanReduction.Basic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `val y < (val x)^2` for a point of negative valuation on an integral Weierstrass curve

Silverman, *AEC*, VII.2.2 (the easy half).  Let `R` be a discrete valuation ring with fraction
field `K`, `val R K` the `ℤᵐ⁰`-valued valuation of `K` at the maximal ideal of `R` (so that
`val R K x ≤ 1` means `x` is integral), and let `W/K` be a Weierstrass curve which is integral
over `R`, so that all its coefficients `aᵢ` satisfy `val R K aᵢ ≤ 1`.

If `(x, y)` is a point of `W` whose `x`-coordinate has **negative valuation** (`1 < val R K x`),
then `val R K y < val R K x * val R K x`.

The argument is pure "dominant term" bookkeeping in the Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`.  Writing `a = val R K x > 1` and `b = val R K y`,
and arguing by contradiction from `a² ≤ b`:

* every monomial of the right-hand side has valuation `< a³`, so `val` of the right-hand side is
  `a³` (`Valuation.map_add_eq_of_lt_left`);
* `b ≥ a² > a`, so the term `y²` dominates `a₁xy` and `a₃y` on the left-hand side, whence `val`
  of the left-hand side is `b²`;
* the equation therefore gives `b² = a³`; but `a² ≤ b` gives `a⁴ ≤ b² = a³ < a⁴`, absurd.

-/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.SilvermanReduction

theorem val_y_lt_sq_of_equation {K : Type*} [Field K]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve.Affine K} [W.IsIntegral R] {x y : K}
    (h : W.Equation x y) (hx : 1 < Work.SilvermanReduction.val R K x) :
    Work.SilvermanReduction.val R K y <
      Work.SilvermanReduction.val R K x * Work.SilvermanReduction.val R K x := by
  by_contra hcon
  rw [not_lt] at hcon
  -- `hcon : val x * val x ≤ val y`
  have h1 : (1 : ℤᵐ⁰) < val R K x := hx
  have hxsq1 : (1 : ℤᵐ⁰) < val R K x * val R K x := one_lt_mul h1.le h1
  have hb1 : (1 : ℤᵐ⁰) < val R K y := lt_of_lt_of_le hxsq1 hcon
  have hxy : val R K x < val R K y :=
    lt_of_lt_of_le (lt_mul_of_one_lt_right (lt_trans zero_lt_one h1) h1) hcon
  -- ## the right-hand side `x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆` has valuation `x ^ 3`
  have h2 : val R K (W.a₂ * x ^ 2) < val R K x ^ 3 := by
    calc val R K (W.a₂ * x ^ 2)
        ≤ (1 : ℤᵐ⁰) * val R K x ^ 2 := by
          rw [map_mul, Valuation.map_pow]
          exact mul_le_mul' (isIntegralK_a₂) le_rfl
      _ = val R K x ^ 2 := one_mul _
      _ < val R K x ^ 3 := pow_lt_pow_right₀ h1 (by norm_num)
  have h4 : val R K (W.a₄ * x) < val R K x ^ 3 := by
    calc val R K (W.a₄ * x)
        ≤ (1 : ℤᵐ⁰) * val R K x := by
          rw [map_mul]
          exact mul_le_mul' (isIntegralK_a₄) le_rfl
      _ = val R K x := one_mul _
      _ < val R K x ^ 3 := by
          simpa using pow_lt_pow_right₀ h1 (by norm_num : (1 : ℕ) < 3)
  have h6 : val R K W.a₆ < val R K x ^ 3 := by
    calc val R K W.a₆ ≤ (1 : ℤᵐ⁰) := isIntegralK_a₆
      _ < val R K x ^ 3 := by
          simpa using pow_lt_pow_right₀ h1 (by norm_num : (0 : ℕ) < 3)
  have step1 : val R K (x ^ 3 + W.a₂ * x ^ 2) = val R K x ^ 3 :=
    (Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_pow]; exact h2)).trans
      (Valuation.map_pow _ _ _)
  have step2 : val R K (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x) = val R K x ^ 3 :=
    (Valuation.map_add_eq_of_lt_left _ (by rw [step1]; exact h4)).trans step1
  have step3 : val R K (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = val R K x ^ 3 :=
    (Valuation.map_add_eq_of_lt_left _ (by rw [step2]; exact h6)).trans step2
  -- ## the left-hand side `y ^ 2 + a₁ * x * y + a₃ * y` has valuation `y ^ 2`
  have hy2 : val R K (y ^ 2) = val R K y ^ 2 := Valuation.map_pow _ _ _
  have ha1xy : val R K (W.a₁ * x * y) < val R K y ^ 2 := by
    have hle : val R K (W.a₁ * x * y) ≤ val R K x * val R K y := by
      rw [map_mul, map_mul]
      calc val R K W.a₁ * val R K x * val R K y
          ≤ (1 : ℤᵐ⁰) * val R K x * val R K y :=
            mul_le_mul' (mul_le_mul' isIntegralK_a₁ le_rfl) le_rfl
        _ = val R K x * val R K y := by rw [one_mul]
    refine lt_of_le_of_lt hle ?_
    rw [pow_two]
    exact mul_lt_mul_of_pos_right hxy (lt_trans zero_lt_one hb1)
  have ha3y : val R K (W.a₃ * y) < val R K y ^ 2 := by
    have hle : val R K (W.a₃ * y) ≤ val R K y := by
      rw [map_mul]
      calc val R K W.a₃ * val R K y ≤ (1 : ℤᵐ⁰) * val R K y :=
            mul_le_mul' isIntegralK_a₃ le_rfl
        _ = val R K y := one_mul _
    refine lt_of_le_of_lt hle ?_
    rw [pow_two]
    exact lt_mul_of_one_lt_right (lt_trans zero_lt_one hb1) hb1
  have hlhs : val R K (y ^ 2 + W.a₁ * x * y + W.a₃ * y) = val R K y ^ 2 := by
    have hmid : val R K (y ^ 2 + W.a₁ * x * y) = val R K y ^ 2 :=
      (Valuation.map_add_eq_of_lt_left _ (by rw [hy2]; exact ha1xy)).trans hy2
    exact (Valuation.map_add_eq_of_lt_left _ (by rw [hmid]; exact ha3y)).trans hmid
  -- ## the two sides agree, so `y ^ 2 = x ^ 3`
  have hb2 : val R K y ^ 2 = val R K x ^ 3 := by
    rw [WeierstrassCurve.Affine.equation_iff] at h
    have hc := congrArg (val R K) h
    rw [hlhs, step3] at hc
    exact hc
  -- ## but `x ^ 2 ≤ y` forces `x ^ 4 ≤ y ^ 2 = x ^ 3 < x ^ 4`
  have h4le : val R K x ^ 4 ≤ val R K x ^ 3 := by
    calc val R K x ^ 4 = (val R K x * val R K x) * (val R K x * val R K x) := by
            rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
      _ ≤ val R K y * val R K y := mul_le_mul' hcon hcon
      _ = val R K y ^ 2 := (pow_two _).symm
      _ = val R K x ^ 3 := hb2
  have h34 : val R K x ^ 3 < val R K x ^ 4 := pow_lt_pow_right₀ h1 (by norm_num)
  exact absurd h4le (not_le.mpr h34)

end Work.SilvermanReduction
