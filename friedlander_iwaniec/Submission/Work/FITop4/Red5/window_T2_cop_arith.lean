import Mathlib

namespace Work.FITop4.Red5

theorem window_T2_cop_arith (C : ℝ) (hC : 0 < C) (x N Mn Pz : ℕ)
    (hx : 4 ≤ x) (hN : 1 ≤ N) (hMn : 1 ≤ Mn) (hPz : 2 ≤ Pz)
    (hN2 : ((N : ℝ)) ^ (2:ℕ) ≤ (x : ℝ)) :
    1600 * (2 * (Mn : ℝ) * (N : ℝ)) ^ ((1:ℝ)/4)
        * (1 + Real.sqrt (Mn : ℝ) / ((Pz : ℝ) * Real.sqrt (N : ℝ)))
        * (Real.log (2 * (N : ℝ)) / Real.log 2)
        * (C * (Real.sqrt (N : ℝ) + (N : ℝ)) * (Real.log (2 + (N : ℝ))) ^ (9:ℕ))
      ≤ (3200 * C * (2:ℝ) ^ ((1:ℝ)/4) * 3 ^ (10:ℕ) / Real.log 2 + 1)
        * ((Mn : ℝ) ^ ((1:ℝ)/4) * (N : ℝ) ^ ((5:ℝ)/4)
            + (Pz : ℝ)⁻¹ * (Mn : ℝ) ^ ((3:ℝ)/4) * (N : ℝ) ^ ((3:ℝ)/4))
        * (Real.log (x : ℝ)) ^ (100:ℕ) := by
  set m : ℝ := (Mn : ℝ) with hm
  set n : ℝ := (N : ℝ) with hn
  set p : ℝ := (Pz : ℝ) with hp
  set X : ℝ := (x : ℝ) with hX
  set U : ℝ := m ^ ((1:ℝ)/4) * n ^ ((5:ℝ)/4) + p⁻¹ * m ^ ((3:ℝ)/4) * n ^ ((3:ℝ)/4) with hU
  set K : ℝ := 3200 * C * (2:ℝ) ^ ((1:ℝ)/4) * 3 ^ (10:ℕ) / Real.log 2 + 1 with hK
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast hMn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast hN
  have hp2 : 2 ≤ p := by rw [hp]; exact_mod_cast hPz
  have hX4 : 4 ≤ X := by rw [hX]; exact_mod_cast hx
  have hn0 : 0 ≤ n := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hpp : 0 < p := by linarith
  have hnp : 0 < n := by linarith
  have hmp : 0 < m := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hnle : n ≤ Real.sqrt X := Real.le_sqrt_of_sq_le hN2
  have hsX2 : (2:ℝ) ≤ Real.sqrt X := Real.le_sqrt_of_sq_le (by nlinarith : (2:ℝ)^2 ≤ X)
  have h2sqrt : 2 * Real.sqrt X ≤ X := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.sqrt X)
        (by linarith : (0:ℝ) ≤ Real.sqrt X - 2), Real.sq_sqrt hX0]
  have h2n_le : 2 * n ≤ X := by linarith [hnle, h2sqrt]
  have h2pn_le : 2 + n ≤ X := by nlinarith [hnle, hsX2, Real.sq_sqrt hX0]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2n_le : Real.log (2*n) ≤ Real.log X := Real.log_le_log (by linarith) h2n_le
  have hlog2pn_le : Real.log (2+n) ≤ Real.log X := Real.log_le_log (by linarith) h2pn_le
  have hlog2pn_nn : 0 ≤ Real.log (2+n) := Real.log_nonneg (by linarith)
  have hlog9 : (Real.log (2+n))^9 ≤ (Real.log X)^9 := pow_le_pow_left₀ hlog2pn_nn hlog2pn_le 9
  have hLX0 : 0 ≤ Real.log X := le_trans hlog2pn_nn hlog2pn_le
  have hLX1 : 1 ≤ Real.log X := by
    have hlog4 : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) hX4
    have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.log_pow 2 2]; norm_num
    linarith [Real.log_two_gt_d9, hlog4, hlog4eq]
  have hLX90 : 1 ≤ (Real.log X)^90 := one_le_pow₀ hLX1
  have hLXpow : (Real.log X)^10 ≤ (Real.log X)^100 := by
    have h100 : (Real.log X)^100 = (Real.log X)^10 * (Real.log X)^90 := by
      rw [show (100:ℕ) = 10 + 90 by norm_num, pow_add]
    rw [h100]; nlinarith [hLX90, pow_nonneg hLX0 10]
  have hLX10' : (Real.log X)^10 = Real.log X * (Real.log X)^9 := by
    rw [show (10:ℕ) = 1 + 9 by norm_num, pow_add, pow_one]
  have hlogD : Real.log (2*n)/Real.log 2 ≤ Real.log X / Real.log 2 :=
    div_le_div_of_nonneg_right hlog2n_le (le_of_lt hlog2pos)
  have hsnn : Real.sqrt n ≤ n := by
    have h1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
    calc Real.sqrt n = Real.sqrt n * 1 := by ring
      _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg n)
      _ = n := by rw [← sq, Real.sq_sqrt hn0]
  have hidn : n ^ ((1:ℝ)/4) * n = n ^ ((5:ℝ)/4) := by
    have h := Real.rpow_add hnp ((1:ℝ)/4) 1
    rw [Real.rpow_one] at h
    rw [show (1:ℝ)/4 + 1 = (5:ℝ)/4 by norm_num] at h
    exact h.symm
  have hidn3 : n ^ ((1:ℝ)/4) * n ^ ((1:ℝ)/2) = n ^ ((3:ℝ)/4) := by
    have h := Real.rpow_add hnp ((1:ℝ)/4) ((1:ℝ)/2)
    rw [show (1:ℝ)/4 + 1/2 = (3:ℝ)/4 by norm_num] at h
    exact h.symm
  have hidm3 : m ^ ((1:ℝ)/4) * m ^ ((1:ℝ)/2) = m ^ ((3:ℝ)/4) := by
    have h := Real.rpow_add hmp ((1:ℝ)/4) ((1:ℝ)/2)
    rw [show (1:ℝ)/4 + 1/2 = (3:ℝ)/4 by norm_num] at h
    exact h.symm
  have h2_4 : (2:ℝ)^((5:ℝ)/4) = 2 * 2^((1:ℝ)/4) := by
    rw [show (5:ℝ)/4 = 1 + 1/4 by norm_num, Real.rpow_add (by norm_num : (0:ℝ) < 2),
        Real.rpow_one]
  have hA : (2*m*n) ^ ((1:ℝ)/4) = 2^((1:ℝ)/4) * m^((1:ℝ)/4) * n^((1:ℝ)/4) := by
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 2*m) (by positivity : (0:ℝ) ≤ n)]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ m)]
  have hT1 : (2*m*n)^((1:ℝ)/4) * (Real.sqrt n + n) ≤
      (2:ℝ)^((5:ℝ)/4) * (m^((1:ℝ)/4)*n^((5:ℝ)/4)) := by
    rw [hA]
    have h1 : Real.sqrt n + n ≤ 2 * n := by linarith [hsnn]
    calc 2^((1:ℝ)/4) * m^((1:ℝ)/4) * n^((1:ℝ)/4) * (Real.sqrt n + n)
        ≤ 2^((1:ℝ)/4) * m^((1:ℝ)/4) * n^((1:ℝ)/4) * (2*n) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2:ℝ)^((5:ℝ)/4) * (m^((1:ℝ)/4) * n^((5:ℝ)/4)) := by
            rw [show 2^((1:ℝ)/4)*m^((1:ℝ)/4)*n^((1:ℝ)/4)*(2*n)
                   = (2 * 2^((1:ℝ)/4)) * m^((1:ℝ)/4) * (n^((1:ℝ)/4)*n) by ring]
            rw [← h2_4, ← hidn]
            ring
  have hT2 : (2*m*n)^((1:ℝ)/4) * (Real.sqrt m/(p*Real.sqrt n)) * (Real.sqrt n + n)
      ≤ (2:ℝ)^((5:ℝ)/4) * (p⁻¹ * m^((3:ℝ)/4) * n^((3:ℝ)/4)) := by
    have hsnn2 : Real.sqrt n + n = Real.sqrt n * (1 + Real.sqrt n) := by
      rw [mul_add, mul_one, ← sq, Real.sq_sqrt hn0]
    have h3 : 1 + Real.sqrt n ≤ 2 * Real.sqrt n := by
      have : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
      linarith
    rw [hsnn2]
    have heq : (2*m*n)^((1:ℝ)/4) * (Real.sqrt m/(p*Real.sqrt n)) * (Real.sqrt n*(1+Real.sqrt n))
        = (2*m*n)^((1:ℝ)/4) * Real.sqrt m / p * (1 + Real.sqrt n) := by
      field_simp
    rw [heq]
    calc (2*m*n)^((1:ℝ)/4) * Real.sqrt m / p * (1 + Real.sqrt n)
        ≤ (2*m*n)^((1:ℝ)/4) * Real.sqrt m / p * (2 * Real.sqrt n) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (2:ℝ)^((5:ℝ)/4) * (p⁻¹ * m^((3:ℝ)/4) * n^((3:ℝ)/4)) := by
            rw [hA, Real.sqrt_eq_rpow m, Real.sqrt_eq_rpow n, div_eq_mul_inv]
            rw [show 2^((1:ℝ)/4) * m^((1:ℝ)/4) * n^((1:ℝ)/4) * m^((1:ℝ)/2) * p⁻¹
                    * (2 * n^((1:ℝ)/2))
                   = (2 * 2^((1:ℝ)/4)) * (m^((1:ℝ)/4) * m^((1:ℝ)/2))
                     * (n^((1:ℝ)/4) * n^((1:ℝ)/2)) * p⁻¹ by ring]
            rw [← h2_4, ← hidm3, ← hidn3]
            ring
  have hABU : (2*m*n)^((1:ℝ)/4) * (1 + Real.sqrt m/(p*Real.sqrt n)) * (Real.sqrt n + n)
      ≤ 2^((5:ℝ)/4) * U := by
    rw [hU]
    rw [show (2*m*n)^((1:ℝ)/4) * (1 + Real.sqrt m/(p*Real.sqrt n)) * (Real.sqrt n + n)
        = (2*m*n)^((1:ℝ)/4) * (Real.sqrt n + n)
          + (2*m*n)^((1:ℝ)/4) * (Real.sqrt m/(p*Real.sqrt n)) * (Real.sqrt n + n) by ring]
    refine le_trans (add_le_add hT1 hT2) (le_of_eq ?_)
    ring
  have hKge : 1600 * 2^((5:ℝ)/4) * C / Real.log 2 ≤ K := by
    rw [hK]
    have h1 : 1600 * 2^((5:ℝ)/4) * C / Real.log 2 = 3200 * 2^((1:ℝ)/4) * C / Real.log 2 := by
      rw [h2_4]; ring
    rw [h1]
    have hnum_le : (3200:ℝ) * 2^((1:ℝ)/4) * C ≤ 3200 * C * 2^((1:ℝ)/4) * 3^(10:ℕ) := by
      have h3 : (1:ℝ) ≤ 3^(10:ℕ) := one_le_pow₀ (by norm_num)
      calc (3200:ℝ) * 2^((1:ℝ)/4) * C = (3200 * 2^((1:ℝ)/4) * C) * 1 := by ring
        _ ≤ (3200 * 2^((1:ℝ)/4) * C) * 3^(10:ℕ) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 3200 * C * 2^((1:ℝ)/4) * 3^(10:ℕ) := by ring
    linarith [div_le_div_of_nonneg_right hnum_le (le_of_lt hlog2pos)]
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hKpos : 0 ≤ K := by rw [hK]; positivity
  have hP'0 : 0 ≤ (2:ℝ)^((5:ℝ)/4) * U := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hU0
  have hD0 : 0 ≤ Real.log (2*n)/Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) (le_of_lt hlog2pos)
  have hD'0 : 0 ≤ Real.log X / Real.log 2 := div_nonneg hLX0 (le_of_lt hlog2pos)
  have hS0 : 0 ≤ (Real.log (2+n))^9 := pow_nonneg hlog2pn_nn 9
  have hS'0 : 0 ≤ (Real.log X)^9 := pow_nonneg hLX0 9
  have hC0 : 0 ≤ C := le_of_lt hC
  calc
    1600 * (2*m*n)^((1:ℝ)/4) * (1 + Real.sqrt m/(p*Real.sqrt n)) * (Real.log (2*n)/Real.log 2)
        * (C * (Real.sqrt n + n) * (Real.log (2+n))^9)
      = 1600 * ((2*m*n)^((1:ℝ)/4) * (1 + Real.sqrt m/(p*Real.sqrt n)) * (Real.sqrt n + n))
          * (Real.log (2*n)/Real.log 2) * C * (Real.log (2+n))^9 := by ring
    _ ≤ 1600 * (2^((5:ℝ)/4) * U) * (Real.log X / Real.log 2) * C * (Real.log X)^9 := by
          gcongr
    _ = (1600 * 2^((5:ℝ)/4) * C / Real.log 2) * (U * (Real.log X)^10) := by
          rw [hLX10']; ring
    _ ≤ K * (U * (Real.log X)^100) := by
          calc (1600 * 2^((5:ℝ)/4) * C / Real.log 2) * (U * (Real.log X)^10)
              ≤ K * (U * (Real.log X)^10) := mul_le_mul_of_nonneg_right hKge (by positivity)
            _ ≤ K * (U * (Real.log X)^100) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLXpow hU0) hKpos
    _ = K * U * (Real.log X)^(100:ℕ) := by ring

end Work.FITop4.Red5
