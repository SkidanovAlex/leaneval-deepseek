import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

/-- The `(D)`-channel coefficient arithmetic `(B)`.

Write `u := (κ * ℓ)⁻¹`.  The two sides differ by the positive common factor
`u ^ (2 * M₀ - 3)` and by the exponent bookkeeping
`ℓ ^ 3 * u ^ 22 = (κ ^ (-(2 * 11))) * (ℓ ^ (3 / 2 - 2 * 11) * ℓ ^ (3 / 2))`, so after
dividing by `u ^ (2 * M₀ - 3)` the claim becomes

`A * C₂ * (1 + κ ^ (2 * M₀ + 22)) * κ ^ (-22) * ℓ ^ (3 / 2 - 22) ≤ Cst * (1 + κ ^ (2 * M₀))`,

which follows from `hbound` once one observes that
`(1 + κ ^ (2 * M₀ + 22)) * κ ^ (-22) ≤ (1 + κ ^ (-22)) * (1 + κ ^ (2 * M₀))`
(equivalently `κ ^ (-22) + κ ^ (2 * M₀) ≤ 1 + κ ^ (-22) + κ ^ (2 * M₀) + κ ^ (2 * M₀ - 22)`)
and that the hypothesis `harith` reads, with `u ^ 22 * ℓ ^ 3 = κ ^ (-22) * ℓ ^ (-19)`
only after the same bookkeeping, as the comparison `(1 + κ ^ (-22)) * ℓ ^ (3 / 2 - 22) ≤ Λ ^ (3 / 2 - 22) + a ^ (3 / 2)`.

`hM₀` is genuinely used: the identity `2 * M₀ - 3 + 22 = 2 * M₀ + 19` needs `3 ≤ 2 * M₀`. -/
theorem chDimg_coefB {A C₂ Cst Λ a κ ℓ : ℝ} {M₀ : ℕ} (hM₀ : 2 ≤ M₀) (hA : 0 ≤ A) (hC₂ : 0 ≤ C₂)
    (hCst : 0 ≤ Cst) (hℓ : 0 < ℓ) (hκ : 0 < κ)
    (harith : (1 + κ ^ (-(2 * (11 : ℤ)))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ))
      ≤ Λ ^ ((3 : ℝ) / 2 - 22) + a ^ (3 / 2 : ℝ))
    (hbound : A * C₂ * (Λ ^ ((3 : ℝ) / 2 - 22) + a ^ (3 / 2 : ℝ)) ≤ Cst) :
    ℓ ^ 3 * A * (C₂ * (1 + κ ^ (2 * (M₀ + 11))) * ((κ * ℓ)⁻¹) ^ (2 * M₀ + 19))
      ≤ Cst * (1 + κ ^ (2 * M₀)) * ((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) * ℓ ^ (3 / 2 : ℝ) := by
  have hκ0 : (0 : ℝ) ≤ κ := hκ.le
  have hℓ0 : (0 : ℝ) ≤ ℓ := hℓ.le
  have _hCst : (0 : ℝ) ≤ Cst := hCst
  have hAC : 0 ≤ A * C₂ := mul_nonneg hA hC₂
  -- the inequality of the hypotheses, with the arithmetic factor split off
  have hQ : A * C₂ * (1 + κ ^ (-(2 * (11 : ℤ)))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ)) ≤ Cst := by
    rw [mul_assoc]
    exact le_trans (mul_le_mul_of_nonneg_left harith hAC) hbound
  -- `κ ^ (-(2 * 11)) = (κ ^ 22)⁻¹`
  have hKi : κ ^ (-(2 * (11 : ℤ))) = (κ ^ 22)⁻¹ := by
    rw [show (2 * (11 : ℤ)) = 22 by norm_num, zpow_neg]
    rfl
  -- the elementary coefficient inequality `(1 + κ^{2M₀+22}) κ^{-22} ≤ (1 + κ^{-22})(1 + κ^{2M₀})`
  have hpow : (1 + κ ^ (2 * (M₀ + 11))) * κ ^ (-(2 * (11 : ℤ)))
      ≤ (1 + κ ^ (-(2 * (11 : ℤ)))) * (1 + κ ^ (2 * M₀)) := by
    rw [hKi, show (2 * (M₀ + 11) : ℕ) = 2 * M₀ + 22 by omega, pow_add]
    have hz : κ ^ 22 * (κ ^ 22)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 22 (ne_of_gt hκ))
    have hzp : 0 < (κ ^ 22)⁻¹ := inv_pos.mpr (pow_pos hκ 22)
    have hx : 0 ≤ κ ^ (2 * M₀) := pow_nonneg hκ0 _
    have h1 : (1 + κ ^ (2 * M₀) * κ ^ 22) * (κ ^ 22)⁻¹ = (κ ^ 22)⁻¹ + κ ^ (2 * M₀) := by
      rw [add_mul, one_mul, mul_assoc, hz, mul_one]
    rw [h1]
    nlinarith [mul_nonneg hzp.le hx]
  -- the coefficient comparison of the target
  have hkey : A * C₂ * (1 + κ ^ (2 * (M₀ + 11))) * κ ^ (-(2 * (11 : ℤ))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ))
      ≤ Cst * (1 + κ ^ (2 * M₀)) := by
    have hmid : A * C₂ * (1 + κ ^ (2 * (M₀ + 11))) * κ ^ (-(2 * (11 : ℤ))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ))
        = A * C₂ * ((1 + κ ^ (2 * (M₀ + 11))) * κ ^ (-(2 * (11 : ℤ)))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ)) := by
      ring
    rw [hmid]
    calc A * C₂ * ((1 + κ ^ (2 * (M₀ + 11))) * κ ^ (-(2 * (11 : ℤ)))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ))
        ≤ A * C₂ * ((1 + κ ^ (-(2 * (11 : ℤ)))) * (1 + κ ^ (2 * M₀))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hAC) (Real.rpow_nonneg hℓ0 _)
      _ = (A * C₂ * (1 + κ ^ (-(2 * (11 : ℤ)))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ))) * (1 + κ ^ (2 * M₀)) := by
          ring
      _ ≤ Cst * (1 + κ ^ (2 * M₀)) := by
          exact mul_le_mul_of_nonneg_right hQ (by positivity)
  -- `(ℓ ^ 22)⁻¹ * ℓ ^ 3 = ℓ ^ (-19)`
  have hpp : (ℓ ^ 22)⁻¹ * ℓ ^ 3 = ℓ ^ (-(19 : ℤ)) := by
    have e1 : (ℓ ^ 22)⁻¹ = ℓ ^ (-(22 : ℤ)) := by rw [zpow_neg]; rfl
    rw [e1]
    change ℓ ^ (-(22 : ℤ)) * ℓ ^ ((3 : ℤ)) = ℓ ^ (-(19 : ℤ))
    rw [← zpow_add₀ (ne_of_gt hℓ) (-(22 : ℤ)) (3 : ℤ)]
    rw [show (-(22 : ℤ) + (3 : ℤ)) = -(19 : ℤ) by norm_num]
  -- `ℓ ^ (3/2 - 22) * ℓ ^ (3/2) = ℓ ^ (-19)`
  have hrp : ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ)) * ℓ ^ (3 / 2 : ℝ) = ℓ ^ (-(19 : ℤ)) := by
    rw [← Real.rpow_add hℓ]
    rw [show (3 : ℝ) / 2 - 2 * (11 : ℝ) + (3 / 2 : ℝ) = (((-(19 : ℤ)) : ℤ) : ℝ) by norm_num]
    exact Real.rpow_intCast ℓ (-(19 : ℤ))
  -- the exponent bookkeeping `u ^ 22 * ℓ ^ 3 = κ ^ (-22) * (ℓ ^ (3/2 - 22) * ℓ ^ (3/2))`
  have hcore : ((κ * ℓ)⁻¹) ^ 22 * ℓ ^ 3
      = κ ^ (-(2 * (11 : ℤ))) * (ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ)) * ℓ ^ (3 / 2 : ℝ)) := by
    rw [inv_pow, mul_pow, mul_inv, mul_assoc]
    rw [hKi, hpp, hrp]
  have hfac : ((κ * ℓ)⁻¹) ^ (2 * M₀ + 19) * ℓ ^ 3
      = ((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) *
          (κ ^ (-(2 * (11 : ℤ))) * (ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ)) * ℓ ^ (3 / 2 : ℝ))) := by
    rw [show 2 * M₀ + 19 = (2 * M₀ - 3) + 22 by omega, pow_add, mul_assoc, hcore]
  -- the common positive factor
  have hW : 0 ≤ ((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) * ℓ ^ (3 / 2 : ℝ) :=
    mul_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr (mul_pos hκ hℓ))) _) (Real.rpow_nonneg hℓ0 _)
  have hL : ℓ ^ 3 * A * (C₂ * (1 + κ ^ (2 * (M₀ + 11))) * ((κ * ℓ)⁻¹) ^ (2 * M₀ + 19))
      = (A * C₂ * (1 + κ ^ (2 * (M₀ + 11))) * κ ^ (-(2 * (11 : ℤ))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ)))
        * (((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) * ℓ ^ (3 / 2 : ℝ)) := by
    have h1 : ℓ ^ 3 * A * (C₂ * (1 + κ ^ (2 * (M₀ + 11))) * ((κ * ℓ)⁻¹) ^ (2 * M₀ + 19))
        = (A * C₂ * (1 + κ ^ (2 * (M₀ + 11)))) * (((κ * ℓ)⁻¹) ^ (2 * M₀ + 19) * ℓ ^ 3) := by ring
    rw [h1, hfac]
    ring
  have hR : Cst * (1 + κ ^ (2 * M₀)) * ((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) * ℓ ^ (3 / 2 : ℝ)
      = (Cst * (1 + κ ^ (2 * M₀))) * (((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) * ℓ ^ (3 / 2 : ℝ)) := by ring
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_right hkey hW

end Work.BoseBoxFock.PCFU
