import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem chDimg_caseArith {a t κ ℓ : ℝ} {j : ℕ} (hj : 11 ≤ j) (ha : 0 < a) (ht : 0 < t)
    (hℓ : ℓ = a * t ^ (-(163 / 323) : ℝ)) (hκℓ : κ * ℓ = t ^ (-(12 / 323) : ℝ))
    (hΛ : max a 1 ≤ ℓ) :
    (1 + κ ^ (-(2 * (j : ℤ)))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (j : ℝ))
      ≤ (max a 1) ^ ((3 : ℝ) / 2 - 2 * (j : ℝ)) + a ^ ((3 : ℝ) / 2) := by
  have hℓpos : 0 < ℓ := by rw [hℓ]; positivity
  have hApos : 0 < max a 1 := lt_of_lt_of_le zero_lt_one (le_max_right a 1)
  have hjR : (11 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  -- `max a 1 ≤ ℓ = a·t^{-163/323}` forces `t ≤ 1`
  have ht1 : t ≤ 1 := by
    have hle : a ≤ ℓ := le_trans (le_max_left a 1) hΛ
    rw [hℓ] at hle
    have hratio : 1 ≤ t ^ (-(163 / 323) : ℝ) := by
      have h : a * 1 ≤ a * t ^ (-(163 / 323) : ℝ) := by linarith [hle]
      exact (mul_le_mul_iff_of_pos_left ha).mp h
    rcases le_or_gt t 1 with h | h
    · exact h
    · exfalso
      have hlt : t ^ (-(163 / 323) : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg h (by norm_num)
      linarith
  have hκpos : 0 < κ := by
    have h : κ = t ^ (-(12 / 323) : ℝ) * ℓ⁻¹ := by
      rw [← hκℓ]; field_simp
    rw [h]; positivity
  -- the `zpow`-`rpow` bridge on `κ`
  have hz1 : κ ^ (-(2 * (j : ℤ))) = κ ^ (-(2 * (j : ℝ))) := by
    have h1 : ((-(2 * (j : ℤ)) : ℤ) : ℝ) = -(2 * (j : ℝ)) := by push_cast; ring
    calc κ ^ (-(2 * (j : ℤ))) = κ ^ (((-(2 * (j : ℤ)) : ℤ) : ℝ)) :=
          (Real.rpow_intCast κ _).symm
      _ = κ ^ (-(2 * (j : ℝ))) := by rw [h1]
  have hmul : κ ^ (-(2 * (j : ℝ))) * ℓ ^ (-(2 * (j : ℝ)))
      = t ^ ((-(12 / 323 : ℝ)) * (-(2 * (j : ℝ)))) := by
    rw [← Real.mul_rpow hκpos.le hℓpos.le]
    rw [hκℓ, ← Real.rpow_mul ht.le]
  have hL : ℓ ^ ((3 : ℝ) / 2) = a ^ ((3 : ℝ) / 2) * t ^ ((-(163 / 323 : ℝ)) * ((3 : ℝ) / 2)) := by
    rw [hℓ]
    rw [Real.mul_rpow ha.le (Real.rpow_nonneg ht.le _)]
    rw [← Real.rpow_mul ht.le]
  have hexp : (-(12 / 323 : ℝ)) * (-(2 * (j : ℝ))) + (-(163 / 323 : ℝ)) * ((3 : ℝ) / 2)
      = (48 * (j : ℝ) - 489) / 646 := by ring
  -- the exact evaluation of the second summand
  have hkey : κ ^ (-(2 * (j : ℤ))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (j : ℝ))
      = a ^ ((3 : ℝ) / 2) * t ^ ((48 * (j : ℝ) - 489) / 646) := by
    rw [hz1]
    calc κ ^ (-(2 * (j : ℝ))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (j : ℝ))
        = κ ^ (-(2 * (j : ℝ))) * (ℓ ^ (-(2 * (j : ℝ))) * ℓ ^ ((3 : ℝ) / 2)) := by
            rw [show (3 : ℝ) / 2 - 2 * (j : ℝ) = (-(2 * (j : ℝ))) + (3 : ℝ) / 2 by ring]
            rw [Real.rpow_add hℓpos]
      _ = (κ ^ (-(2 * (j : ℝ))) * ℓ ^ (-(2 * (j : ℝ)))) * ℓ ^ ((3 : ℝ) / 2) := by ring
      _ = t ^ ((-(12 / 323 : ℝ)) * (-(2 * (j : ℝ)))) * ℓ ^ ((3 : ℝ) / 2) := by rw [hmul]
      _ = t ^ ((-(12 / 323 : ℝ)) * (-(2 * (j : ℝ))))
            * (a ^ ((3 : ℝ) / 2) * t ^ ((-(163 / 323 : ℝ)) * ((3 : ℝ) / 2))) := by rw [hL]
      _ = a ^ ((3 : ℝ) / 2)
            * (t ^ ((-(12 / 323 : ℝ)) * (-(2 * (j : ℝ))))
                * t ^ ((-(163 / 323 : ℝ)) * ((3 : ℝ) / 2))) := by ring
      _ = a ^ ((3 : ℝ) / 2)
            * t ^ ((-(12 / 323 : ℝ)) * (-(2 * (j : ℝ))) + (-(163 / 323 : ℝ)) * ((3 : ℝ) / 2)) := by
            rw [Real.rpow_add ht]
      _ = a ^ ((3 : ℝ) / 2) * t ^ ((48 * (j : ℝ) - 489) / 646) := by rw [hexp]
  -- first summand: `ℓ^{3/2-2j} ≤ (max a 1)^{3/2-2j}`
  have hneg : (3 : ℝ) / 2 - 2 * (j : ℝ) ≤ 0 := by linarith
  have h1 : ℓ ^ ((3 : ℝ) / 2 - 2 * (j : ℝ)) ≤ (max a 1) ^ ((3 : ℝ) / 2 - 2 * (j : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hApos hΛ hneg
  -- second summand: `t^{(48j-489)/646} ≤ 1`, `48j - 489 ≥ 39 > 0`
  have hexpnn : 0 ≤ (48 * (j : ℝ) - 489) / 646 := by
    apply div_nonneg _ (by norm_num); linarith
  have htle : t ^ ((48 * (j : ℝ) - 489) / 646) ≤ 1 := Real.rpow_le_one ht.le ht1 hexpnn
  have h2 : κ ^ (-(2 * (j : ℤ))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (j : ℝ)) ≤ a ^ ((3 : ℝ) / 2) := by
    rw [hkey]
    calc a ^ ((3 : ℝ) / 2) * t ^ ((48 * (j : ℝ) - 489) / 646)
          ≤ a ^ ((3 : ℝ) / 2) * 1 :=
            mul_le_mul_of_nonneg_left htle (Real.rpow_nonneg ha.le _)
      _ = a ^ ((3 : ℝ) / 2) := mul_one _
  have hsplit : (1 + κ ^ (-(2 * (j : ℤ)))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (j : ℝ))
      = ℓ ^ ((3 : ℝ) / 2 - 2 * (j : ℝ))
        + κ ^ (-(2 * (j : ℤ))) * ℓ ^ ((3 : ℝ) / 2 - 2 * (j : ℝ)) := by ring
  rw [hsplit]
  linarith

end Work.BoseBoxFock.PCFU
