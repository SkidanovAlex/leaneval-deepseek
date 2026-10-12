import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.farLinArith` — the far-slot scalar arithmetic of FS §9

The far part of the residual word is dominated by the quantity
`128π√101 · |ρ−μ| · a · √(ρℓ³) · √𝓜`, which has to be absorbed by the budget
`(10^300/4)·((ρ+μ)a𝓜 + (ρ+μ)^{3/2} a √(ℓ³𝓜))`.

Since `a > 0` is a common factor it can be cancelled, and the remaining
inequality is pure monotonicity in the diluteness parameters:

* `|ρ − μ| ≤ ρ + μ` (both signs of `ρ − μ` are `≤ ρ + μ`, as `μ ≥ 0` and `ρ ≥ 0`),
* `√ρ ≤ √(ρ+μ)` (`ρ ≤ ρ + μ`),
* `√(ρℓ³) = √ρ·√(ℓ³)` and `√(ℓ³𝓜) = √(ℓ³)·√𝓜` (multiplicativity of the square
  root on nonnegative arguments),
* `(ρ+μ)^{3/2} = (ρ+μ)·√(ρ+μ)`,
* the numerical constant `128π√101 ≤ 10^300/4` (from `π < 4` and `√101 ≤ 11`).

Consequently `LHS ≤ 128π√101·(ρ+μ)^{3/2}√(ℓ³𝓜) ≤ (10^300/4)·(ρ+μ)^{3/2}√(ℓ³𝓜)`,
and the second summand of the budget already dominates this.
-/

namespace Work.BoseFixR

theorem farLinArith {ρ μ ℓ M a : ℝ} (hρ : 0 ≤ ρ) (hμ : 0 < μ) (hℓ : 0 ≤ ℓ) (hM : 0 ≤ M) (ha : 0 < a) :
    128 * Real.pi * Real.sqrt 101 * |ρ - μ| * a * Real.sqrt (ρ * ℓ ^ 3) * Real.sqrt M
      ≤ 10 ^ 300 / 4 * ((ρ + μ) * a * M + (ρ + μ) ^ (3 / 2 : ℝ) * a * Real.sqrt (ℓ ^ 3 * M)) := by
  have hℓ3 : 0 ≤ ℓ ^ 3 := by positivity
  have hρμ0 : 0 ≤ ρ + μ := by linarith
  have hρμpos : 0 < ρ + μ := by linarith
  have hρμ : ρ ≤ ρ + μ := by linarith
  -- multiplicative splittings of the two square roots
  have hs1 : Real.sqrt (ρ * ℓ ^ 3) = Real.sqrt ρ * Real.sqrt (ℓ ^ 3) := Real.sqrt_mul hρ _
  have hs2 : Real.sqrt (ℓ ^ 3 * M) = Real.sqrt (ℓ ^ 3) * Real.sqrt M := Real.sqrt_mul hℓ3 M
  -- `(ρ+μ)^{3/2} = (ρ+μ)·√(ρ+μ)`
  have hpow : (ρ + μ) ^ (3 / 2 : ℝ) = (ρ + μ) * Real.sqrt (ρ + μ) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hρμpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    ring
  -- `|ρ−μ| ≤ ρ+μ`
  have habs : |ρ - μ| ≤ ρ + μ := by
    rw [abs_le]
    constructor <;> linarith
  -- the constant
  have h101 : Real.sqrt 101 ≤ 11 := by
    have h : Real.sqrt 101 ≤ Real.sqrt (11 ^ 2 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 11)] at h
  -- `128π√101 ≤ 5632 ≤ 25000 = 10^5/4 ≤ 10^300/4`; the last step avoids evaluating
  -- `10^300` by pure monotonicity of division (`linear` arithmetic cannot reduce a
  -- power whose exponent exceeds Lean's exponentiation threshold).
  have h56 : 128 * Real.pi * Real.sqrt 101 ≤ 5632 := by
    nlinarith [Real.pi_lt_four, h101, Real.pi_pos, Real.sqrt_nonneg (101 : ℝ)]
  have hc : 128 * Real.pi * Real.sqrt 101 ≤ 10 ^ 300 / 4 := by
    have h1 : (10 : ℝ) ^ 5 ≤ 10 ^ 300 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h2 : (10 : ℝ) ^ 5 / 4 ≤ 10 ^ 300 / 4 := div_le_div_of_nonneg_right h1 (by norm_num)
    have h3 : ((10 : ℝ) ^ 5 / 4 : ℝ) = 25000 := by norm_num
    rw [h3] at h2
    exact le_trans h56 (le_trans (by norm_num : (5632 : ℝ) ≤ 25000) h2)
  have hKnn : (0 : ℝ) ≤ 10 ^ 300 / 4 :=
    div_nonneg (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 10) 300)) (by norm_num)
  have hmain : 128 * Real.pi * Real.sqrt 101 * |ρ - μ| * Real.sqrt (ρ * ℓ ^ 3) * Real.sqrt M
      ≤ 10 ^ 300 / 4 * ((ρ + μ) * M + (ρ + μ) ^ (3 / 2 : ℝ) * Real.sqrt (ℓ ^ 3 * M)) := by
    rw [hs1, hs2, hpow]
    -- `|ρ−μ|·√ρ ≤ (ρ+μ)·√(ρ+μ)`
    have hX : |ρ - μ| * Real.sqrt ρ ≤ (ρ + μ) * Real.sqrt (ρ + μ) :=
      mul_le_mul habs (Real.sqrt_le_sqrt hρμ) (Real.sqrt_nonneg ρ) hρμ0
    have hcX : 128 * Real.pi * Real.sqrt 101 * (|ρ - μ| * Real.sqrt ρ)
        ≤ 10 ^ 300 / 4 * ((ρ + μ) * Real.sqrt (ρ + μ)) :=
      mul_le_mul hc hX (by positivity) (by positivity)
    -- collect the remaining nonnegative factor `√(ℓ³)·√𝓜`
    have hA : 128 * Real.pi * Real.sqrt 101 * |ρ - μ| * (Real.sqrt ρ * Real.sqrt (ℓ ^ 3))
          * Real.sqrt M
        ≤ (10 ^ 300 / 4 * ((ρ + μ) * Real.sqrt (ρ + μ))) * (Real.sqrt (ℓ ^ 3) * Real.sqrt M) := by
      calc 128 * Real.pi * Real.sqrt 101 * |ρ - μ| * (Real.sqrt ρ * Real.sqrt (ℓ ^ 3))
            * Real.sqrt M
          = (128 * Real.pi * Real.sqrt 101 * (|ρ - μ| * Real.sqrt ρ))
              * (Real.sqrt (ℓ ^ 3) * Real.sqrt M) := by ring
        _ ≤ (10 ^ 300 / 4 * ((ρ + μ) * Real.sqrt (ρ + μ)))
              * (Real.sqrt (ℓ ^ 3) * Real.sqrt M) :=
            mul_le_mul_of_nonneg_right hcX (by positivity)
    -- the budget's second summand already dominates this
    have hB : (10 ^ 300 / 4 * ((ρ + μ) * Real.sqrt (ρ + μ)))
          * (Real.sqrt (ℓ ^ 3) * Real.sqrt M)
        ≤ 10 ^ 300 / 4 * ((ρ + μ) * M
            + (ρ + μ) * Real.sqrt (ρ + μ) * (Real.sqrt (ℓ ^ 3) * Real.sqrt M)) := by
      have hle : (ρ + μ) * Real.sqrt (ρ + μ) * (Real.sqrt (ℓ ^ 3) * Real.sqrt M)
          ≤ (ρ + μ) * M
            + (ρ + μ) * Real.sqrt (ρ + μ) * (Real.sqrt (ℓ ^ 3) * Real.sqrt M) :=
        le_add_of_nonneg_left (by positivity)
      calc (10 ^ 300 / 4 * ((ρ + μ) * Real.sqrt (ρ + μ)))
            * (Real.sqrt (ℓ ^ 3) * Real.sqrt M)
          = 10 ^ 300 / 4 * ((ρ + μ) * Real.sqrt (ρ + μ)
              * (Real.sqrt (ℓ ^ 3) * Real.sqrt M)) := by ring
        _ ≤ 10 ^ 300 / 4 * ((ρ + μ) * M
              + (ρ + μ) * Real.sqrt (ρ + μ) * (Real.sqrt (ℓ ^ 3) * Real.sqrt M)) :=
            mul_le_mul_of_nonneg_left hle hKnn
    linarith [hA, hB]
  -- multiply back by `a > 0`
  have hmul := mul_le_mul_of_nonneg_right hmain ha.le
  calc 128 * Real.pi * Real.sqrt 101 * |ρ - μ| * a * Real.sqrt (ρ * ℓ ^ 3) * Real.sqrt M
      = (128 * Real.pi * Real.sqrt 101 * |ρ - μ| * Real.sqrt (ρ * ℓ ^ 3) * Real.sqrt M) * a := by
        ring
    _ ≤ (10 ^ 300 / 4 * ((ρ + μ) * M + (ρ + μ) ^ (3 / 2 : ℝ) * Real.sqrt (ℓ ^ 3 * M))) * a :=
        hmul
    _ = 10 ^ 300 / 4 * ((ρ + μ) * a * M
          + (ρ + μ) ^ (3 / 2 : ℝ) * a * Real.sqrt (ℓ ^ 3 * M)) := by ring

end Work.BoseFixR
