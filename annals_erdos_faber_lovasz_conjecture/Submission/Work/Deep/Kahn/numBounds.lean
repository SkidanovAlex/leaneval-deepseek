import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.NibbleRoundDefs

/-!
# The numerical side conditions of one Kahn round

`Work.Deep.Kahn.numBounds` collects the four elementary numerical estimates that the
regularised one-round nibble needs, in the regime of the iteration: `D ≥ 10^30`,
`Λ ≥ (1+ε) D`, `η K ≤ 1` (with `K ≥ 2`) and `η⁻¹ ≤ D^{1/9}`, and with
`retention Λ C D K = (1 - 1/(KΛ))^{CD}` the list-retention factor of one round.

The estimates are

1. `D^{1/4} + log 2 ≤ η² Λ / 64`,
2. `16 ≤ η² Λ`,
3. `1 ≤ Λ (1 - retention) + η Λ`,
4. `Λ (1 - retention) + η Λ ≤ 2 Λ`.

The content is the chain `D^{7/9} ≤ η² Λ` coming from `η ≥ D^{-1/9}` and `Λ ≥ D`
(together with `D^{7/9} = D^{1/2} · D^{5/18} ≥ D^{1/2} ≥ 128`), which dominates both the
`64 (D^{1/4} + log 2)` of (1) and the constant `16` of (2); and the two-sided bound
`0 ≤ retention ≤ 1` of the retention factor, which turns (3) into `1 ≤ η Λ` (from
`η Λ ≥ D^{8/9} ≥ 1`) and (4) into `η ≤ 1`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

theorem numBounds {C D Λ K : ℕ} {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hD1 : 1 ≤ D) (hΛ1 : 1 ≤ Λ) (hK2 : 2 ≤ K)
    (hηK : η * (K : ℝ) ≤ 1)
    (hDΛ : (1 + ε) * (D : ℝ) ≤ (Λ : ℝ))
    (hD : (10 : ℝ) ^ 30 ≤ (D : ℝ))
    (hηinv : η⁻¹ ≤ (D : ℝ) ^ ((1 : ℝ) / 9)) :
    (D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 2 ≤ η ^ 2 * (Λ : ℝ) / 64 ∧
    16 ≤ η ^ 2 * (Λ : ℝ) ∧
    1 ≤ (Λ : ℝ) * (1 - retention Λ C D K) + η * (Λ : ℝ) ∧
    (Λ : ℝ) * (1 - retention Λ C D K) + η * (Λ : ℝ) ≤ 2 * (Λ : ℝ) := by
  -- ### elementary cast facts
  have hK1R : (1:ℝ) ≤ (K:ℝ) := by
    have h : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK2
    linarith
  have hK2R : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK2
  have hΛ1R : (1:ℝ) ≤ (Λ:ℝ) := by exact_mod_cast hΛ1
  have hD1R : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD1
  have hD0 : (0:ℝ) < (D:ℝ) := lt_of_lt_of_le zero_lt_one hD1R
  have hDnonneg : (0:ℝ) ≤ (D:ℝ) := le_of_lt hD0
  -- ### `Λ ≥ D`
  have hLxD : (D:ℝ) ≤ (Λ:ℝ) := by
    have h : (D:ℝ) ≤ (1+ε)*(D:ℝ) := by
      have h1 : (1:ℝ) ≤ 1 + ε := by linarith
      calc (D:ℝ) = 1 * (D:ℝ) := (one_mul _).symm
        _ ≤ (1+ε) * (D:ℝ) := mul_le_mul_of_nonneg_right h1 hDnonneg
    linarith [h, hDΛ]
  -- ### `η ≥ D^{-1/9}`
  have hD9pos : (0:ℝ) < (D:ℝ) ^ ((1:ℝ)/9) := Real.rpow_pos_of_pos hD0 _
  have hηinvpos : (0:ℝ) < η⁻¹ := inv_pos.mpr hη
  have hηgeinv : ((D:ℝ) ^ ((1:ℝ)/9))⁻¹ ≤ η := by
    have h := inv_anti₀ hηinvpos hηinv
    rwa [inv_inv] at h
  -- ### `η ≤ 1` (from `η K ≤ 1` and `K ≥ 2`)
  have hηle1 : η ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hK2R (le_of_lt hη)
    linarith [h, hηK]
  -- ### `D^{7/9} ≤ η² Λ`
  have hη2a : ((D:ℝ) ^ ((2:ℝ)/9))⁻¹ ≤ η ^ 2 := by
    have hstep : ((D:ℝ) ^ ((1:ℝ)/9))⁻¹ * ((D:ℝ) ^ ((1:ℝ)/9))⁻¹ ≤ η * η :=
      mul_le_mul hηgeinv hηgeinv (le_of_lt (inv_pos.mpr hD9pos)) (le_of_lt hη)
    have he : ((2:ℝ)/9) = (1:ℝ)/9 + (1:ℝ)/9 := by norm_num
    have h2a : (D:ℝ) ^ ((2:ℝ)/9) = (D:ℝ) ^ ((1:ℝ)/9) * (D:ℝ) ^ ((1:ℝ)/9) := by
      rw [he, Real.rpow_add hD0]
    rw [h2a, mul_inv, pow_two]
    exact hstep
  have h79 : (D:ℝ) ^ ((7:ℝ)/9) = ((D:ℝ) ^ ((2:ℝ)/9))⁻¹ * (D:ℝ) := by
    have he : ((7:ℝ)/9) = (1:ℝ) - (2:ℝ)/9 := by norm_num
    rw [he, Real.rpow_sub hD0, Real.rpow_one, div_eq_mul_inv]
    exact mul_comm _ _
  have h79le : (D:ℝ) ^ ((7:ℝ)/9) ≤ η ^ 2 * (Λ:ℝ) := by
    rw [h79]
    exact mul_le_mul hη2a hLxD hDnonneg (sq_nonneg η)
  -- ### `D^{8/9} ≤ η Λ`, hence `1 ≤ η Λ`
  have h89 : (D:ℝ) ^ ((8:ℝ)/9) = ((D:ℝ) ^ ((1:ℝ)/9))⁻¹ * (D:ℝ) := by
    have he : ((8:ℝ)/9) = (1:ℝ) - (1:ℝ)/9 := by norm_num
    rw [he, Real.rpow_sub hD0, Real.rpow_one, div_eq_mul_inv]
    exact mul_comm _ _
  have h89le : (D:ℝ) ^ ((8:ℝ)/9) ≤ η * (Λ:ℝ) := by
    rw [h89]
    exact mul_le_mul hηgeinv hLxD hDnonneg (le_of_lt hη)
  have h1D89 : (1:ℝ) ≤ (D:ℝ) ^ ((8:ℝ)/9) := Real.one_le_rpow hD1R (by norm_num)
  have hηL1 : (1:ℝ) ≤ η * (Λ:ℝ) := le_trans h1D89 h89le
  -- ### `128 ≤ D^{1/2}` (from `128² ≤ 10^30 ≤ D`)
  have h128 : (128:ℝ) ≤ (D:ℝ) ^ ((1:ℝ)/2) := by
    have hsq : (128:ℝ) ^ 2 ≤ (D:ℝ) := by
      have h : (128:ℝ) ^ 2 ≤ (10:ℝ) ^ 30 := by norm_num
      linarith [h, hD]
    have hs : Real.sqrt ((128:ℝ)^2) ≤ Real.sqrt (D:ℝ) := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 128)] at hs
    rwa [Real.sqrt_eq_rpow] at hs
  -- ### monotonicity of the power functions
  have hD14ge1 : (1:ℝ) ≤ (D:ℝ) ^ ((1:ℝ)/4) := Real.one_le_rpow hD1R (by norm_num)
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have h128Dh : (128:ℝ) * (D:ℝ) ^ ((1:ℝ)/4) ≤
      (D:ℝ) ^ ((1:ℝ)/4) * (D:ℝ) ^ ((1:ℝ)/2) := by
    calc (128:ℝ) * (D:ℝ)^((1:ℝ)/4) = (D:ℝ)^((1:ℝ)/4) * 128 := mul_comm _ _
      _ ≤ (D:ℝ)^((1:ℝ)/4) * (D:ℝ)^((1:ℝ)/2) :=
          mul_le_mul_of_nonneg_left h128 (Real.rpow_nonneg hDnonneg _)
  have hA3 : (D:ℝ) ^ ((1:ℝ)/4) * (D:ℝ) ^ ((1:ℝ)/2) = (D:ℝ) ^ ((3:ℝ)/4) := by
    have he : ((3:ℝ)/4) = (1:ℝ)/4 + (1:ℝ)/2 := by norm_num
    rw [he, Real.rpow_add hD0]
  have h34le : (D:ℝ) ^ ((3:ℝ)/4) ≤ (D:ℝ) ^ ((7:ℝ)/9) :=
    Real.rpow_le_rpow_of_exponent_le hD1R (by norm_num)
  have h12le : (D:ℝ) ^ ((1:ℝ)/2) ≤ (D:ℝ) ^ ((7:ℝ)/9) :=
    Real.rpow_le_rpow_of_exponent_le hD1R (by norm_num)
  -- ### (1)  `D^{1/4} + log 2 ≤ η² Λ / 64`
  have hAgoal : (D:ℝ) ^ ((1:ℝ)/4) + Real.log 2 ≤ η ^ 2 * (Λ:ℝ) / 64 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 64)]
    have heq : ((D:ℝ)^((1:ℝ)/4) + Real.log 2) * 64 =
        64 * ((D:ℝ)^((1:ℝ)/4) + Real.log 2) := mul_comm _ _
    rw [heq]
    calc (64:ℝ) * ((D:ℝ)^((1:ℝ)/4) + Real.log 2)
        ≤ 128 * (D:ℝ)^((1:ℝ)/4) := by
          have h := mul_le_mul_of_nonneg_left (le_trans hlog hD14ge1)
            (by norm_num : (0:ℝ) ≤ 64)
          have h2 : (64:ℝ) * ((D:ℝ)^((1:ℝ)/4) + Real.log 2)
              = 64 * (D:ℝ)^((1:ℝ)/4) + 64 * Real.log 2 := by ring
          rw [h2]; linarith
      _ ≤ (D:ℝ)^((1:ℝ)/4) * (D:ℝ)^((1:ℝ)/2) := h128Dh
      _ = (D:ℝ)^((3:ℝ)/4) := hA3
      _ ≤ (D:ℝ)^((7:ℝ)/9) := h34le
      _ ≤ η ^ 2 * (Λ:ℝ) := h79le
  -- ### (2)  `16 ≤ η² Λ`
  have hBgoal : (16:ℝ) ≤ η ^ 2 * (Λ:ℝ) := by
    have h1 : (16:ℝ) ≤ (128:ℝ) := by norm_num
    exact le_trans (le_trans (le_trans h1 h128) h12le) h79le
  -- ### the retention factor lies in `[0,1]`
  have hbase0 : (0:ℝ) ≤ 1 - (1/(K:ℝ))/(Λ:ℝ) := by
    have hKL1 : (1:ℝ) ≤ (K:ℝ) * (Λ:ℝ) := by
      have h := mul_le_mul hK1R hΛ1R (by norm_num : (0:ℝ) ≤ 1) (Nat.cast_nonneg K)
      simpa using h
    have h1 : (1/(K:ℝ))/(Λ:ℝ) = ((K:ℝ)*(Λ:ℝ))⁻¹ := by
      rw [one_div, div_eq_mul_inv, mul_inv]
    rw [h1]
    have h2 : ((K:ℝ)*(Λ:ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hKL1
    linarith
  have hbase1 : 1 - (1/(K:ℝ))/(Λ:ℝ) ≤ 1 :=
    sub_le_self _ (div_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg K))
      (Nat.cast_nonneg Λ))
  have hs0 : (0:ℝ) ≤ retention Λ C D K := by rw [retention]; exact pow_nonneg hbase0 _
  have hs1 : retention Λ C D K ≤ 1 := by
    rw [retention]; exact pow_le_one₀ hbase0 hbase1
  -- ### (3)  `1 ≤ Λ (1 - retention) + η Λ`
  have hCgoal : 1 ≤ (Λ:ℝ) * (1 - retention Λ C D K) + η * (Λ:ℝ) := by
    have h1 : (0:ℝ) ≤ (Λ:ℝ) * (1 - retention Λ C D K) :=
      mul_nonneg (Nat.cast_nonneg Λ) (by linarith)
    linarith [h1, hηL1]
  -- ### (4)  `Λ (1 - retention) + η Λ ≤ 2 Λ`
  have hDgoal : (Λ:ℝ) * (1 - retention Λ C D K) + η * (Λ:ℝ) ≤ 2 * (Λ:ℝ) := by
    have h1 : (Λ:ℝ) * (1 - retention Λ C D K) ≤ (Λ:ℝ) := by
      have h := mul_le_mul_of_nonneg_left (by linarith : 1 - retention Λ C D K ≤ 1)
        (Nat.cast_nonneg Λ)
      rwa [mul_one] at h
    have h2 : η * (Λ:ℝ) ≤ (Λ:ℝ) := by
      have h := mul_le_mul_of_nonneg_right hηle1 (Nat.cast_nonneg Λ)
      rwa [one_mul] at h
    linarith
  exact ⟨hAgoal, hBgoal, hCgoal, hDgoal⟩

end

end Work.Deep.Kahn
