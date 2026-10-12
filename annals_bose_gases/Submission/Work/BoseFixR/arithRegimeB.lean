import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

theorem arithRegimeB {s X : ℝ} (hs : 1 ≤ s) (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hsX : X ^ 3 ≤ s)
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ 1 / 6) :
    (10 : ℝ) ^ 300 * ((s + 2) * X ^ (337 / 4 : ℝ)
        + (s + 2) ^ (3 / 2 : ℝ) * X ^ (337 / 8 : ℝ))
      + 256 * Real.pi * s * X ^ (337 / 4 : ℝ) + Real.pi * X ^ 6
      ≤ 4 * Real.pi * s ^ 2 := by
  have h10pos : (0:ℝ) ≤ (10:ℝ)^300 := by positivity
  have hspos : (0:ℝ) ≤ s := by linarith
  have hs2pos : (0:ℝ) ≤ s + 2 := by linarith
  -- `X ^ a` is monotone decreasing in `a` for `0 < X ≤ 1`
  have hpow1 : X ^ (337/4:ℝ) ≤ X ^ (289/8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by norm_num)
  have hpow2 : X ^ (337/8:ℝ) ≤ X ^ (289/8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by norm_num)
  -- the two large prefactors are absorbed by the slack hypothesis
  have hA : (10:ℝ)^300 * X ^ (337/4:ℝ) ≤ 1/6 :=
    le_trans (mul_le_mul_of_nonneg_left hpow1 h10pos) hslack
  have hB : (10:ℝ)^300 * X ^ (337/8:ℝ) ≤ 1/6 :=
    le_trans (mul_le_mul_of_nonneg_left hpow2 h10pos) hslack
  -- first term, bounded by `s^2`
  have ht1 : (10:ℝ)^300 * ((s+2) * X ^ (337/4:ℝ)) ≤ (s+2) * (1/6) := by
    rw [← mul_assoc, mul_comm ((10:ℝ)^300) (s+2), mul_assoc]
    exact mul_le_mul_of_nonneg_left hA hs2pos
  have hb1 : (s+2) * (1/6) ≤ s^2 := by nlinarith [sq_nonneg (s-1), hs]
  have hA1 : (10:ℝ)^300 * ((s+2) * X ^ (337/4:ℝ)) ≤ s^2 := le_trans ht1 hb1
  -- second term, bounded by `(3/2) * s^2`
  have ht2 : (10:ℝ)^300 * ((s+2)^(3/2:ℝ) * X ^ (337/8:ℝ))
      ≤ (s+2)^(3/2:ℝ) * (1/6) := by
    rw [← mul_assoc, mul_comm ((10:ℝ)^300) ((s+2)^(3/2:ℝ)), mul_assoc]
    exact mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hs2pos _)
  have h9 : (s+2) ^ (3/2:ℝ) ≤ 9 * s^2 := by
    have hle : s + 2 ≤ 3 * s := by linarith
    have h1 : (s+2) ^ (3/2:ℝ) ≤ (3*s) ^ (3/2:ℝ) :=
      Real.rpow_le_rpow hs2pos hle (by norm_num)
    have h2 : (3*s) ^ (3/2:ℝ) ≤ (3*s) ^ ((2:ℕ):ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ 3*s) (by norm_num)
    rw [Real.rpow_natCast] at h2
    have h3 : (3*s)^(2:ℕ) = 9 * s^2 := by ring
    linarith
  have hb2 : (s+2)^(3/2:ℝ) * (1/6) ≤ (3/2) * s^2 := by nlinarith [h9]
  have hA2 : (10:ℝ)^300 * ((s+2)^(3/2:ℝ) * X ^ (337/8:ℝ)) ≤ (3/2) * s^2 :=
    le_trans ht2 hb2
  -- the `X^(289/8)` factor is absolutely small
  have h6m : 6 * ((10:ℝ)^300 * X ^ (289/8:ℝ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hslack (by norm_num : (0:ℝ) ≤ 6)
    have h66 : (6:ℝ) * (1/6) = 1 := by norm_num
    rwa [h66] at h
  have hX289 : X ^ (289/8:ℝ) ≤ 1/(6 * (10:ℝ)^300) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 6 * (10:ℝ)^300)]
    calc X ^ (289/8:ℝ) * (6 * (10:ℝ)^300) = 6 * ((10:ℝ)^300 * X ^ (289/8:ℝ)) := by
          ring
      _ ≤ 1 := h6m
  have hXp : X ^ (337/4:ℝ) ≤ 1/(6 * (10:ℝ)^300) := le_trans hpow1 hX289
  have hpi : 256 * Real.pi ≤ 1024 := by nlinarith [Real.pi_lt_four]
  have h1024 : (1024:ℝ) ≤ (10:ℝ)^300 := by
    have h1 : (10:ℝ)^4 ≤ (10:ℝ)^300 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h2 : (1024:ℝ) ≤ (10:ℝ)^4 := by norm_num
    exact le_trans h2 h1
  have h6T : (10:ℝ)^300 ≤ 6 * (10:ℝ)^300 :=
    le_mul_of_one_le_left (by positivity) (by norm_num)
  have hcoef : 256 * Real.pi * (1/(6*(10:ℝ)^300)) ≤ 1 := by
    have hden : (0:ℝ) < 6 * (10:ℝ)^300 := by positivity
    rw [mul_one_div, div_le_iff₀ hden, one_mul]
    exact le_trans hpi (le_trans h1024 h6T)
  -- third term, bounded by `s^2`
  have h3a : 256 * Real.pi * s * X^(337/4:ℝ)
      ≤ 256 * Real.pi * s * (1/(6*(10:ℝ)^300)) :=
    mul_le_mul_of_nonneg_left hXp (by positivity)
  have h3b : 256 * Real.pi * s * (1/(6*(10:ℝ)^300)) ≤ s := by
    calc 256 * Real.pi * s * (1/(6*(10:ℝ)^300))
        = (256 * Real.pi * (1/(6*(10:ℝ)^300))) * s := by ring
      _ ≤ 1 * s := mul_le_mul_of_nonneg_right hcoef hspos
      _ = s := by ring
  have hsle : s ≤ s^2 := by nlinarith [hs]
  have hA3 : 256 * Real.pi * s * X^(337/4:ℝ) ≤ s^2 := le_trans (le_trans h3a h3b) hsle
  -- fourth term, bounded by `π * s^2`
  have hA4 : Real.pi * X^6 ≤ Real.pi * s^2 := by
    have hX6 : X^6 ≤ 1 := pow_le_one₀ (le_of_lt hX0) hX1
    have hs1 : (1:ℝ) ≤ s^2 := one_le_pow₀ hs
    exact le_trans (mul_le_mul_of_nonneg_left hX6 (le_of_lt Real.pi_pos))
                   (mul_le_mul_of_nonneg_left hs1 (le_of_lt Real.pi_pos))
  -- assembly: each of the four terms is at most a multiple of `s^2`
  have hsum : (10:ℝ)^300 * ((s+2) * X ^ (337/4:ℝ))
        + (10:ℝ)^300 * ((s+2)^(3/2:ℝ) * X ^ (337/8:ℝ))
        + 256 * Real.pi * s * X ^ (337/4:ℝ) + Real.pi * X^6
      ≤ s^2 + (3/2) * s^2 + s^2 + Real.pi * s^2 :=
    add_le_add (add_le_add (add_le_add hA1 hA2) hA3) hA4
  have hnum : s^2 + (3/2) * s^2 + s^2 + Real.pi * s^2 ≤ 4 * Real.pi * s^2 := by
    nlinarith [Real.pi_gt_three, sq_nonneg s]
  rw [show (10:ℝ)^300 * ((s+2) * X ^ (337/4:ℝ) + (s+2)^(3/2:ℝ) * X ^ (337/8:ℝ))
        = (10:ℝ)^300 * ((s+2) * X ^ (337/4:ℝ))
          + (10:ℝ)^300 * ((s+2)^(3/2:ℝ) * X ^ (337/8:ℝ)) by ring]
  exact le_trans hsum hnum

end Work.BoseFixR
