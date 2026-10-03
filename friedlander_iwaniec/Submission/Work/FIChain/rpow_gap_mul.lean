import Mathlib
import Submission.Work.FITop.RCPrelude

namespace Work.FIChain

/-- For `0 < η < 1/32`, eventually `(2 x^{5/16})^{1-η} ≤ (x^{5/16-3η/32}/4)^{1-η/4}`.
The two sides have `x`-exponents differing by `g = 9η/64 + 3η²/128 > 0`, so the
left side dominates only up to a bounded factor `2^{1-η}4^{1-η/4}` which the
polynomial gain `x^{-g}` eventually beats. -/
theorem rpow_gap_mul (η : ℝ) (hη : 0 < η) (hη16 : η < 1 / 32) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) ^ (1 - η)
        ≤ ((x : ℝ) ^ ((5 : ℝ) / 16 - 3 * η / 32) / 4) ^ (1 - η / 4) := by
  set eL : ℝ := ((5 : ℝ) / 16) * (1 - η) with heL
  set eR : ℝ := ((5 : ℝ) / 16 - 3 * η / 32) * (1 - η / 4) with heR
  set g : ℝ := eR - eL with hg
  have hgpos : 0 < g := by
    rw [hg, heR, heL]
    nlinarith [hη, sq_nonneg η]
  have htend : Filter.Tendsto (fun x : ℕ => (x : ℝ) ^ g) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hgpos).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ x : ℕ in Filter.atTop, 2 ^ (1 - η) * 4 ^ (1 - η / 4) ≤ (x : ℝ) ^ g :=
    htend.eventually (Filter.eventually_ge_atTop (2 ^ (1 - η) * 4 ^ (1 - η / 4)))
  filter_upwards [hev, Filter.eventually_ge_atTop (1 : ℕ)] with x hC hx1
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hx1)
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  have hL : (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) ^ (1 - η) = 2 ^ (1 - η) * (x : ℝ) ^ eL := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hxnn _), ← Real.rpow_mul hxnn, ← heL]
  have hR : ((x : ℝ) ^ ((5 : ℝ) / 16 - 3 * η / 32) / 4) ^ (1 - η / 4)
      = (x : ℝ) ^ eR / 4 ^ (1 - η / 4) := by
    rw [Real.div_rpow (Real.rpow_nonneg hxnn _) (by norm_num), ← Real.rpow_mul hxnn, ← heR]
  have hpow : (x : ℝ) ^ eL = (x : ℝ) ^ eR * (x : ℝ) ^ (-g) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    rw [hg, heL, heR]; ring
  have hg1 : (x : ℝ) ^ g * (x : ℝ) ^ (-g) = 1 := by
    rw [← Real.rpow_add hxpos, add_neg_cancel, Real.rpow_zero]
  have hCx : 2 ^ (1 - η) * 4 ^ (1 - η / 4) * (x : ℝ) ^ (-g) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hxnn (-g))
    rwa [hg1] at h
  rw [hL, hR, le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _), hpow]
  have hrearr : 2 ^ (1 - η) * ((x : ℝ) ^ eR * (x : ℝ) ^ (-g)) * 4 ^ (1 - η / 4)
      = (2 ^ (1 - η) * 4 ^ (1 - η / 4) * (x : ℝ) ^ (-g)) * (x : ℝ) ^ eR := by ring
  rw [hrearr]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hxnn eR) hCx

end Work.FIChain
