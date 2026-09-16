import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.BombieriVinogradov

theorem vaughan_mean_value_param (x Q : ℕ) (hx : 64 ≤ x) (hQ : 2 ≤ Q) (hQx : Q ^ 2 ≤ x) :
    ∃ T : ℕ, 1 ≤ T ∧ (T : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ) ∧
      (T : ℝ) * (Q : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) ∧
      min ((x : ℝ) ^ (1 / 3 : ℝ)) ((x : ℝ) ^ (2 / 3 : ℝ) / (Q : ℝ)) ≤ 2 * (T : ℝ) ∧
      (T : ℝ) ≤ (x : ℝ) := by
  have hxr : (64 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  -- cube root of x is at least 4
  have h13 : (4 : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ) := by
    have h := Real.rpow_le_rpow (show (0:ℝ) ≤ 64 by norm_num) hxr (show (0:ℝ) ≤ 1/3 by norm_num)
    have h64 : (64 : ℝ) ^ (1/3:ℝ) = 4 := by
      rw [show (64:ℝ) = (4:ℝ)^3 by norm_num]
      rw [← Real.rpow_natCast (4:ℝ) 3]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num
    linarith [h64 ▸ h]
  -- Q <= x^(1/2)
  have hQle : (Q : ℝ) ≤ (x : ℝ) ^ (1/2:ℝ) := by
    have hQR : (0:ℝ) ≤ (Q:ℝ) := le_of_lt hQpos
    have hxr2 : ((Q:ℝ))^2 ≤ (x:ℝ) := by
      have : ((Q^2 : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast hQx
      simpa [Nat.cast_pow] using this
    have hQle_sqrt : (Q:ℝ) ≤ Real.sqrt (x:ℝ) := (Real.le_sqrt hQR (by positivity)).2 hxr2
    have hsqrt : Real.sqrt (x:ℝ) = (x:ℝ)^(1/2:ℝ) := Real.sqrt_eq_rpow (x:ℝ)
    linarith [hQle_sqrt, hsqrt]
  -- sixth root of x is at least 2
  have h16 : (2 : ℝ) ≤ (x : ℝ) ^ (1/6:ℝ) := by
    have h := Real.rpow_le_rpow (show (0:ℝ) ≤ 64 by norm_num) hxr (show (0:ℝ) ≤ 1/6 by norm_num)
    have h64 : (64:ℝ)^(1/6:ℝ) = 2 := by
      rw [show (64:ℝ) = (2:ℝ)^6 by norm_num]
      rw [← Real.rpow_natCast (2:ℝ) 6]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    linarith [h64 ▸ h]
  -- 2Q <= x^(2/3)
  have h23 : 2*(Q:ℝ) ≤ (x:ℝ)^(2/3:ℝ) := by
    have hhalf : (0:ℝ) ≤ (x:ℝ)^(1/2:ℝ) := Real.rpow_nonneg (le_of_lt hxpos) _
    have hsplit : (x:ℝ)^(2/3:ℝ) = (x:ℝ)^(1/2:ℝ) * (x:ℝ)^(1/6:ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    rw [hsplit]
    calc 2*(Q:ℝ) ≤ 2*(x:ℝ)^(1/2:ℝ) := by linarith [hQle]
      _ = (x:ℝ)^(1/2:ℝ) * 2 := by ring
      _ ≤ (x:ℝ)^(1/2:ℝ) * (x:ℝ)^(1/6:ℝ) := mul_le_mul_of_nonneg_left h16 hhalf
  -- the minimum is at least 2
  have hmin2 : (2:ℝ) ≤ min ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ)) := by
    apply le_min
    · linarith
    · rw [le_div_iff₀ hQpos]; linarith [h23]
  -- x^(1/3) <= x
  have h13x : (x:ℝ)^(1/3:ℝ) ≤ (x:ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (1/3:ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  refine ⟨⌊min ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ))⌋₊, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1 <= T
    apply Nat.le_floor
    linarith
  · -- T <= x^(1/3)
    have hTm : ((⌊min ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ))⌋₊ : ℕ) : ℝ)
        ≤ min ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ)) := Nat.floor_le (by linarith)
    have := min_le_left ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ))
    linarith
  · -- T * Q <= x^(2/3)
    have hTm : ((⌊min ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ))⌋₊ : ℕ) : ℝ)
        ≤ min ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ)) := Nat.floor_le (by linarith)
    have hm2 := min_le_right ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ))
    have h := mul_le_mul_of_nonneg_right (le_trans hTm hm2) (le_of_lt hQpos)
    rw [div_mul_cancel₀ ((x:ℝ)^(2/3:ℝ)) (ne_of_gt hQpos)] at h
    exact h
  · -- min <= 2*T
    have hlt : min ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ))
        < ((⌊min ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ))⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    linarith
  · -- T <= x
    have hTm : ((⌊min ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ))⌋₊ : ℕ) : ℝ)
        ≤ min ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ)) := Nat.floor_le (by linarith)
    have := min_le_left ((x:ℝ)^(1/3:ℝ)) ((x:ℝ)^(2/3:ℝ)/(Q:ℝ))
    linarith [h13x]

end Commons.NumberTheory.BombieriVinogradov