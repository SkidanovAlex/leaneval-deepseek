import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.ErrResRegimeA` — the far-regime error budget

Scalar (numerical) lemma: at a far parameter point, the crude error budget `ErrRes`
together with the residual `|ρ - μ|`-term of the `c`-number fits into the far-region
margin `4πa(ρ-μ)²ℓ³`.

With `M = X^{337/4}·(μL³)` (the window parameter `𝓜` above) and `X = (μa³)^{1/323}`
tiny, the three monomials of the budget are paid for as follows (`X ≤ 1`,
`10³⁰⁰X^{289/8} ≤ 1/6`, and `μX³ ≤ |ρ-μ|` from the far condition):

* `10³⁰⁰(ρ+μ)AM ≤ (A L³)·(3/2)μ²X⁶` since `ρ + μ ≤ 3μ` and
  `10³⁰⁰X^{337/4} = (10³⁰⁰X^{289/8})X^{385/8} ≤ X⁶/6`;
* `10³⁰⁰(ρ+μ)^{3/2}A√(L³M) ≤ (A L³)·μ²X⁶` since `√(L³M) = L³X^{337/8}√μ`,
  `(ρ+μ)^{3/2}√μ ≤ 6μ²` and `10³⁰⁰X^{337/8} = (10³⁰⁰X^{289/8})X⁶ ≤ X⁶/6`;
* `256πA|ρ-μ|M ≤ (A L³)·(1/2)(ρ-μ)²` since `X^{337/4} = X^{325/4}X³`,
  `256πX^{325/4} ≤ 256πX^{289/8} ≤ 1/2`, and `μX³ ≤ |ρ-μ|`;
* `πAμ²L³X⁶ ≤ (A L³)·π(ρ-μ)²` since `(μX³)² ≤ |ρ-μ|²`.

Adding up: `LHS ≤ (A L³)(π + 5/2)μ²X⁶ + (A L³)(1/2)(ρ-μ)² ≤ (A L³)(π+3)(ρ-μ)²
≤ 4πA(ρ-μ)²L³`.
-/

set_option exponentiation.threshold 400
set_option linter.unusedVariables false

namespace Work.BoseFixR

/-- The scalar core of `ErrResRegimeA`: with the `A`- and `L³`-factors stripped off
(via `M = X^{337/4}(μL³)` and `√(L³M) = L³X^{337/8}√μ`) the budget is dominated by
`4π(ρ-μ)²`. -/
private lemma errResRegimeA_core {μ ρ X : ℝ}
    (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2 * μ)
    (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hfar : μ * X ^ 3 ≤ |ρ - μ|)
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ 1 / 6) :
    (10 : ℝ) ^ 300 * ((ρ + μ) * (X ^ (337 / 4 : ℝ) * μ))
      + (10 : ℝ) ^ 300 * ((ρ + μ) ^ (3 / 2 : ℝ) * (X ^ (337 / 8 : ℝ) * Real.sqrt μ))
      + 256 * Real.pi * |ρ - μ| * (X ^ (337 / 4 : ℝ) * μ)
      + Real.pi * μ ^ 2 * X ^ 6
      ≤ 4 * Real.pi * (ρ - μ) ^ 2 := by
  -- `(μX³)² ≤ |ρ-μ|²`
  have hD : μ ^ 2 * X ^ 6 ≤ (ρ - μ) ^ 2 := by
    have h3 : (0 : ℝ) ≤ μ * X ^ 3 := by positivity
    have h2 : (μ * X ^ 3) ^ 2 ≤ |ρ - μ| ^ 2 := pow_le_pow_left₀ h3 hfar 2
    have h4 : (μ * X ^ 3) ^ 2 = μ ^ 2 * X ^ 6 := by ring
    rw [h4, sq_abs] at h2
    exact h2
  -- `10³⁰⁰X^{337/4} ≤ X⁶/2`
  have hB1 : (10 : ℝ) ^ 300 * X ^ (337 / 4 : ℝ) ≤ (1 / 2) * X ^ 6 := by
    have hsplit : X ^ (337 / 4 : ℝ) = X ^ (289 / 8 : ℝ) * X ^ (385 / 8 : ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    have hmono : X ^ (385 / 8 : ℝ) ≤ X ^ (6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by norm_num)
    have h385 : 0 ≤ X ^ (385 / 8 : ℝ) := Real.rpow_nonneg hX0.le _
    have h6 : 0 ≤ X ^ 6 := by positivity
    rw [hsplit]
    calc (10 : ℝ) ^ 300 * (X ^ (289 / 8 : ℝ) * X ^ (385 / 8 : ℝ))
        = ((10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ)) * X ^ (385 / 8 : ℝ) := by ring
      _ ≤ (1 / 6) * X ^ (385 / 8 : ℝ) := mul_le_mul_of_nonneg_right hslack h385
      _ ≤ (1 / 6) * X ^ (6 : ℝ) := mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ ≤ (1 / 2) * X ^ 6 := by
          simpa using mul_le_mul_of_nonneg_right (by norm_num : (1 / 6 : ℝ) ≤ 1 / 2) h6
  -- `10³⁰⁰X^{337/8} ≤ X⁶/6`
  have hB2 : (10 : ℝ) ^ 300 * X ^ (337 / 8 : ℝ) ≤ (1 / 6) * X ^ 6 := by
    have hsplit : X ^ (337 / 8 : ℝ) = X ^ (289 / 8 : ℝ) * X ^ 6 := by
      have h1 : X ^ (337 / 8 : ℝ) = X ^ (289 / 8 : ℝ) * X ^ (6 : ℝ) := by
        rw [← Real.rpow_add hX0]; norm_num
      rw [h1, Real.rpow_ofNat X 6]
    rw [hsplit]
    calc (10 : ℝ) ^ 300 * (X ^ (289 / 8 : ℝ) * X ^ 6)
        = ((10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ)) * X ^ 6 := by ring
      _ ≤ (1 / 6) * X ^ 6 := mul_le_mul_of_nonneg_right hslack (by positivity)
  -- `256πX^{325/4} ≤ 1/2`
  have hB3 : 256 * Real.pi * X ^ (325 / 4 : ℝ) ≤ (1 / 2) := by
    have hmono : X ^ (325 / 4 : ℝ) ≤ X ^ (289 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by norm_num)
    have hc : (0 : ℝ) ≤ 256 * Real.pi := by positivity
    have h10 : (0 : ℝ) < 10 ^ 300 := by norm_num
    have hkey : (256 * Real.pi * X ^ (289 / 8 : ℝ)) * 10 ^ 300 ≤ (1 / 2) * 10 ^ 300 := by
      calc (256 * Real.pi * X ^ (289 / 8 : ℝ)) * 10 ^ 300
          = 256 * Real.pi * (10 ^ 300 * X ^ (289 / 8 : ℝ)) := by ring
        _ ≤ 256 * Real.pi * (1 / 6) := mul_le_mul_of_nonneg_left hslack hc
        _ ≤ (1 / 2) * 10 ^ 300 := by nlinarith [Real.pi_lt_four]
    have h289 : 256 * Real.pi * X ^ (289 / 8 : ℝ) ≤ 1 / 2 := le_of_mul_le_mul_right hkey h10
    calc 256 * Real.pi * X ^ (325 / 4 : ℝ) ≤ 256 * Real.pi * X ^ (289 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left hmono hc
      _ ≤ 1 / 2 := h289
  -- `(ρ+μ)^{3/2}√μ ≤ 6μ²`
  have hM2 : (ρ + μ) ^ (3 / 2 : ℝ) * Real.sqrt μ ≤ 6 * μ ^ 2 := by
    have h0 : (0 : ℝ) ≤ ρ + μ := by linarith
    have h3 : ρ + μ ≤ 3 * μ := by linarith
    have h1 : (ρ + μ) ^ (3 / 2 : ℝ) = Real.sqrt ((ρ + μ) ^ 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (ρ + μ) 3, ← Real.rpow_mul h0]
      norm_num
    have h2 : Real.sqrt ((ρ + μ) ^ 3) * Real.sqrt μ = Real.sqrt ((ρ + μ) ^ 3 * μ) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (ρ + μ) ^ 3)]
    rw [h1, h2]
    have hcube : (ρ + μ) ^ 3 ≤ (3 * μ) ^ 3 := pow_le_pow_left₀ h0 h3 3
    have hmain : (ρ + μ) ^ 3 * μ ≤ 27 * μ ^ 4 := by
      calc (ρ + μ) ^ 3 * μ ≤ (3 * μ) ^ 3 * μ := mul_le_mul_of_nonneg_right hcube hμ.le
        _ = 27 * μ ^ 4 := by ring
    refine le_trans (Real.sqrt_le_sqrt hmain) ?_
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 27) (μ ^ 4)]
    have h4 : Real.sqrt (μ ^ 4) = μ ^ 2 := by
      rw [show (μ : ℝ) ^ 4 = (μ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [h4]
    have h27 : Real.sqrt 27 ≤ 6 := by
      rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 6)]
      norm_num
    nlinarith [sq_nonneg μ, Real.sqrt_nonneg 27]
  -- the four termwise bounds
  have hρμ : ρ + μ ≤ 3 * μ := by linarith
  have hP1 : (10 : ℝ) ^ 300 * ((ρ + μ) * (X ^ (337 / 4 : ℝ) * μ)) ≤ (3 / 2) * (μ ^ 2 * X ^ 6) := by
    rw [show (10 : ℝ) ^ 300 * ((ρ + μ) * (X ^ (337 / 4 : ℝ) * μ))
        = ((ρ + μ) * μ) * ((10 : ℝ) ^ 300 * X ^ (337 / 4 : ℝ)) by ring]
    calc ((ρ + μ) * μ) * ((10 : ℝ) ^ 300 * X ^ (337 / 4 : ℝ))
        ≤ (3 * μ * μ) * ((1 / 2) * X ^ 6) := by gcongr
      _ = (3 / 2) * (μ ^ 2 * X ^ 6) := by ring
  have hP2 : (10 : ℝ) ^ 300 * ((ρ + μ) ^ (3 / 2 : ℝ) * (X ^ (337 / 8 : ℝ) * Real.sqrt μ))
      ≤ μ ^ 2 * X ^ 6 := by
    rw [show (10 : ℝ) ^ 300 * ((ρ + μ) ^ (3 / 2 : ℝ) * (X ^ (337 / 8 : ℝ) * Real.sqrt μ))
        = ((ρ + μ) ^ (3 / 2 : ℝ) * Real.sqrt μ) * ((10 : ℝ) ^ 300 * X ^ (337 / 8 : ℝ)) by ring]
    calc ((ρ + μ) ^ (3 / 2 : ℝ) * Real.sqrt μ) * ((10 : ℝ) ^ 300 * X ^ (337 / 8 : ℝ))
        ≤ (6 * μ ^ 2) * ((1 / 6) * X ^ 6) := by gcongr
      _ = μ ^ 2 * X ^ 6 := by ring
  have hP3 : 256 * Real.pi * |ρ - μ| * (X ^ (337 / 4 : ℝ) * μ) ≤ (1 / 2) * (ρ - μ) ^ 2 := by
    have hsplit : X ^ (337 / 4 : ℝ) = X ^ (325 / 4 : ℝ) * X ^ 3 := by
      have h1 : X ^ (337 / 4 : ℝ) = X ^ (325 / 4 : ℝ) * X ^ (3 : ℝ) := by
        rw [← Real.rpow_add hX0]; norm_num
      rw [h1, Real.rpow_ofNat X 3]
    rw [hsplit]
    have hB : |ρ - μ| * μ * X ^ 3 ≤ |ρ - μ| * |ρ - μ| := by
      calc |ρ - μ| * μ * X ^ 3 = |ρ - μ| * (μ * X ^ 3) := by ring
        _ ≤ |ρ - μ| * |ρ - μ| := mul_le_mul_of_nonneg_left hfar (abs_nonneg _)
    calc 256 * Real.pi * |ρ - μ| * (X ^ (325 / 4 : ℝ) * X ^ 3 * μ)
        = (256 * Real.pi * X ^ (325 / 4 : ℝ)) * (|ρ - μ| * μ * X ^ 3) := by ring
      _ ≤ (1 / 2) * (|ρ - μ| * |ρ - μ|) := mul_le_mul hB3 hB (by positivity) (by norm_num)
      _ = (1 / 2) * (ρ - μ) ^ 2 := by rw [← sq_abs]; ring
  have hP4 : Real.pi * μ ^ 2 * X ^ 6 ≤ Real.pi * (ρ - μ) ^ 2 := by
    have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    calc Real.pi * μ ^ 2 * X ^ 6 = Real.pi * (μ ^ 2 * X ^ 6) := by ring
      _ ≤ Real.pi * (ρ - μ) ^ 2 := mul_le_mul_of_nonneg_left hD hpi
  nlinarith [hP1, hP2, hP3, hP4, Real.pi_gt_three]

theorem ErrResRegimeA {A μ ρ L M X : ℝ}
    (hA : 0 < A) (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2 * μ)
    (hL : 0 < L) (hM : 0 < M) (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hfar : μ * X ^ 3 ≤ |ρ - μ|)
    (hML : M = X ^ (337 / 4 : ℝ) * (μ * L ^ 3))
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ 1 / 6) :
    (10 : ℝ) ^ 300 * ((ρ + μ) * A * M
        + (ρ + μ) ^ (3 / 2 : ℝ) * A * Real.sqrt (L ^ 3 * M))
      + |ρ - μ| * (256 * Real.pi * A * M)
      + Real.pi * A * μ ^ 2 * L ^ 3 * X ^ 6
      ≤ 4 * Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by
  -- the square-root factor of the linear/cubic word
  have hsqrt : Real.sqrt (L ^ 3 * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
      = L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ := by
    have hsq : X ^ (337 / 4 : ℝ) = (X ^ (337 / 8 : ℝ)) ^ 2 := by
      rw [sq, ← Real.rpow_add hX0]; norm_num
    have hs1 : Real.sqrt (X ^ (337 / 4 : ℝ)) = X ^ (337 / 8 : ℝ) := by
      rw [hsq, Real.sqrt_sq (Real.rpow_nonneg hX0.le _)]
    have hs2 : Real.sqrt (L ^ 6 * (X ^ (337 / 4 : ℝ) * μ))
        = L ^ 3 * Real.sqrt (X ^ (337 / 4 : ℝ) * μ) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ L ^ 6),
          show L ^ 6 = (L ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ L ^ 3)]
    have hs3 : Real.sqrt (X ^ (337 / 4 : ℝ) * μ) = X ^ (337 / 8 : ℝ) * Real.sqrt μ := by
      rw [Real.sqrt_mul (Real.rpow_nonneg hX0.le _), hs1]
    calc Real.sqrt (L ^ 3 * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
        = Real.sqrt (L ^ 6 * (X ^ (337 / 4 : ℝ) * μ)) := by
          rw [show L ^ 3 * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3))
                = L ^ 6 * (X ^ (337 / 4 : ℝ) * μ) by ring]
      _ = L ^ 3 * Real.sqrt (X ^ (337 / 4 : ℝ) * μ) := hs2
      _ = L ^ 3 * (X ^ (337 / 8 : ℝ) * Real.sqrt μ) := by rw [hs3]
      _ = L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ := by ring
  rw [hML, hsqrt]
  have hAL : (0 : ℝ) ≤ A * L ^ 3 := by positivity
  calc (10 : ℝ) ^ 300 * ((ρ + μ) * A * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3))
          + (ρ + μ) ^ (3 / 2 : ℝ) * A * (L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ))
        + |ρ - μ| * (256 * Real.pi * A * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
        + Real.pi * A * μ ^ 2 * L ^ 3 * X ^ 6
      = (A * L ^ 3) * ((10 : ℝ) ^ 300 * ((ρ + μ) * (X ^ (337 / 4 : ℝ) * μ))
          + (10 : ℝ) ^ 300 * ((ρ + μ) ^ (3 / 2 : ℝ) * (X ^ (337 / 8 : ℝ) * Real.sqrt μ))
          + 256 * Real.pi * |ρ - μ| * (X ^ (337 / 4 : ℝ) * μ)
          + Real.pi * μ ^ 2 * X ^ 6) := by ring
    _ ≤ (A * L ^ 3) * (4 * Real.pi * (ρ - μ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (errResRegimeA_core hμ hρ hρ2 hX0 hX1 hfar hslack) hAL
    _ = 4 * Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by ring

end Work.BoseFixR
