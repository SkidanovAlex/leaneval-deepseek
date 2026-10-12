import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

theorem highMode_arith {KL Λ sℓ μ av ρ w p τ eT : ℝ}
    (hμ : 0 < μ) (ha : 0 < av) (hρ : |ρ| ≤ 2 * μ) (hw : |w| ≤ 16 * Real.pi * av)
    (hKL : 1024 ≤ KL) (hΛ : 4 * (KL * Real.sqrt (μ * av)) ≤ Λ) (hΛp : Λ < p)
    (hsℓ : sℓ ≤ Real.sqrt (μ * av)) (heT : eT ≤ 1 / 2)
    (hτ : (1 - eT) * (max 0 (p - sℓ)) ^ 2 ≤ τ) :
    2 * |ρ * w| ≤ τ := by
  -- μ * av > 0, so that `Real.sqrt (μ * av)` is strictly positive and its square is μ * av.
  have hμav : 0 < μ * av := mul_pos hμ ha
  have hsqrtsq : Real.sqrt (μ * av) ^ 2 = μ * av := Real.sq_sqrt hμav.le
  -- Λ is at least 4096 √(μ av), because KL ≥ 1024.
  have hΛge : 4096 * Real.sqrt (μ * av) ≤ Λ := by
    have h1 : (1024 : ℝ) * Real.sqrt (μ * av) ≤ KL * Real.sqrt (μ * av) :=
      mul_le_mul_of_nonneg_right hKL (Real.sqrt_nonneg _)
    nlinarith [hΛ, h1]
  -- hence p > Λ ≥ 4096 √(μ av), and since sℓ ≤ √(μ av) we get p - sℓ ≥ 4095 √(μ av) ≥ 0.
  have hp_gt : 4096 * Real.sqrt (μ * av) < p := lt_of_le_of_lt hΛge hΛp
  have hpms : 4095 * Real.sqrt (μ * av) ≤ p - sℓ := by nlinarith [hsℓ, hp_gt]
  have hnonneg : 0 ≤ p - sℓ := le_trans (by nlinarith [Real.sqrt_nonneg (μ * av)]) hpms
  have hmax : max 0 (p - sℓ) = p - sℓ := max_eq_right hnonneg
  -- Therefore τ ≥ (1 - eT) * (p - sℓ)^2 ≥ (1/2) * (4095 √(μ av))^2 = (1/2) * 4095^2 * μ * av.
  have hτ1 : (1 / 2 : ℝ) * (4095 * Real.sqrt (μ * av)) ^ 2 ≤ τ := by
    rw [hmax] at hτ
    have hle1 : (1 / 2 : ℝ) ≤ 1 - eT := by linarith
    have hsq : (4095 * Real.sqrt (μ * av)) ^ 2 ≤ (p - sℓ) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith [Real.sqrt_nonneg (μ * av)]) hpms 2
    nlinarith [hτ, hle1, hsq, sq_nonneg (p - sℓ)]
  have hkey : (1 / 2 : ℝ) * (4095 ^ 2 * (μ * av)) ≤ τ := by
    have h2 : (4095 * Real.sqrt (μ * av)) ^ 2 = 4095 ^ 2 * (μ * av) := by
      rw [mul_pow, hsqrtsq]
    linarith [hτ1, h2]
  -- On the other side, |ρ * w| ≤ (2 μ)(16 π av) = 32 π μ av.
  have habs : |ρ * w| ≤ (2 * μ) * (16 * Real.pi * av) := by
    rw [abs_mul]
    exact mul_le_mul hρ hw (abs_nonneg _) (by linarith)
  have hfin : 64 * Real.pi * μ * av ≤ (1 / 2 : ℝ) * (4095 ^ 2 * (μ * av)) := by
    nlinarith [Real.pi_le_four, hμav.le]
  nlinarith [habs, hkey, hfin]

end Work.BoseBogFS
