import Mathlib

set_option autoImplicit false

noncomputable section

namespace Work.HP.badclass

/-- Arithmetic step of the second-moment bound: the Chebyshev inequality together with the first and
second moment estimates yields the paucity of the bad classes. -/
lemma arith_step {n N : ℕ} {p m S T q N0 : ℝ}
    (hn : 3 ≤ n) (hN : n + 1 ≤ N) (hp2 : 2 ≤ p) (hm : (p / 2) ^ (n + 1) ≤ m) (hm0 : 0 < m)
    (hS : m * (p ^ (N - 1) - p ^ (N - (n + 1))) ≤ S)
    (hT : T ≤ m * (m * p ^ (N - 2) + q)) (hq : q = p ^ N)
    (hchev : N0 * S ^ 2 ≤ q * (q * T - S ^ 2)) :
    N0 ≤ (2 ^ (n + 2) + 4) * p ^ (N - n + 1) := by
  have hp0 : 0 < p := by linarith
  have hp0ne : p ≠ 0 := ne_of_gt hp0
  have hp1 : 1 ≤ p := by linarith
  have hpn0 : (0:ℝ) < p ^ n := pow_pos hp0 n
  have hNn : n ≤ N := by omega
  have hqpos : 0 < q := by rw [hq]; positivity
  set eps : ℝ := (p ^ n)⁻¹ with hepsdef
  have heps0 : 0 < eps := by rw [hepsdef]; exact inv_pos.mpr hpn0
  have h8pn : (8:ℝ) ≤ p ^ n := by
    calc (8:ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ p ^ n := pow_le_pow_left₀ (by norm_num) hp2 n
  have heps8 : eps ≤ 1/8 := by
    have h := one_div_le_one_div_of_le (show (0:ℝ) < 8 by norm_num) h8pn
    simpa [hepsdef, one_div] using h
  have hepsq : 1/2 ≤ (1 - eps) ^ 2 := by nlinarith [heps0, heps8]
  have hdeficit : 1 - (1 - eps) ^ 2 ≤ 2 * eps := by nlinarith [heps0, heps8]
  -- `p^(N-(n+1)) = p^(N-1) * eps`
  have hBA : p ^ (N - (n + 1)) = p ^ (N - 1) * eps := by
    rw [hepsdef, ← div_eq_mul_inv, eq_div_iff (ne_of_gt hpn0), ← pow_add]
    congr 1
    omega
  have hApos : 0 < p ^ (N - 1) := by positivity
  have hAB : p ^ (N - 1) - p ^ (N - (n + 1)) = p ^ (N - 1) * (1 - eps) := by
    rw [hBA]; ring
  -- lower bound on S
  have hS2 : m * (p ^ (N - 1) * (1 - eps)) ≤ S := by rw [← hAB]; exact hS
  have hSnn : 0 ≤ m * (p ^ (N - 1) * (1 - eps)) := by
    refine mul_nonneg (le_of_lt hm0) (mul_nonneg (le_of_lt hApos) ?_)
    linarith
  have hSsq_raw : (m * (p ^ (N - 1) * (1 - eps))) ^ 2 ≤ S ^ 2 :=
    pow_le_pow_left₀ hSnn hS2 2
  have hident : (m * (p ^ (N - 1) * (1 - eps))) ^ 2
      = m ^ 2 * p ^ (2 * N - 2) * (1 - eps) ^ 2 := by
    rw [mul_pow, mul_pow, ← pow_mul, show (N - 1) * 2 = 2 * N - 2 by omega]
    ring
  have hSsq : m ^ 2 * p ^ (2 * N - 2) * (1 - eps) ^ 2 ≤ S ^ 2 := by
    rw [← hident]; exact hSsq_raw
  have hSsq' : m ^ 2 * p ^ (2 * N - 2) * (1/2) ≤ S ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hepsq (by positivity)) hSsq
  have hSsqpos : 0 < S ^ 2 := lt_of_lt_of_le (by positivity) hSsq'
  -- upper bound on T
  have hqT : q * T ≤ m ^ 2 * p ^ (2 * N - 2) + m * q ^ 2 := by
    have h1 : q * T ≤ q * (m * (m * p ^ (N - 2) + q)) :=
      mul_le_mul_of_nonneg_left hT (le_of_lt hqpos)
    have h2 : q * (m * (m * p ^ (N - 2) + q)) = m ^ 2 * (q * p ^ (N - 2)) + m * q ^ 2 := by
      ring
    have h3 : q * p ^ (N - 2) = p ^ (2 * N - 2) := by
      rw [hq, ← pow_add]; congr 1; omega
    rw [h2, h3] at h1
    exact h1
  -- key inequality on `q*T - S^2`
  have hQ : q * T - S ^ 2 ≤ 2 * eps * (m ^ 2 * p ^ (2 * N - 2)) + m * q ^ 2 := by
    have h3 : p ^ (2 * N - 2) * (1 - (1 - eps) ^ 2) ≤ p ^ (2 * N - 2) * (2 * eps) :=
      mul_le_mul_of_nonneg_left hdeficit (by positivity)
    have h4 : m ^ 2 * (p ^ (2 * N - 2) * (1 - (1 - eps) ^ 2))
        ≤ m ^ 2 * (p ^ (2 * N - 2) * (2 * eps)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith [hqT, hSsq, h4]
  have hN0le : N0 ≤ q * (q * T - S ^ 2) / S ^ 2 := by
    rw [le_div_iff₀ hSsqpos]
    linarith [hchev]
  have hqeps : q * eps = p ^ (N - n) := by
    rw [hq, hepsdef, ← pow_sub₀ p hp0ne hNn]
  have hq3 : q ^ 3 / (m * p ^ (2 * N - 2)) = p ^ (N + 2) / m := by
    rw [hq, ← pow_mul, show N * 3 = (2 * N - 2) + (N + 2) by omega, pow_add,
      div_eq_div_iff (mul_ne_zero (ne_of_gt hm0) (pow_ne_zero _ hp0ne)) (ne_of_gt hm0)]
    ring
  have hterm1 : 4 * p ^ (N - n) ≤ 4 * p ^ (N - n + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 4)
    exact pow_le_pow_right₀ hp1 (by omega)
  have hterm2 : 2 * p ^ (N + 2) / m ≤ 2 ^ (n + 2) * p ^ (N - n + 1) := by
    have hmpos : 0 < (p / 2) ^ (n + 1) := by positivity
    have h1 : 2 * p ^ (N + 2) / m ≤ 2 * p ^ (N + 2) / (p / 2) ^ (n + 1) :=
      div_le_div_of_nonneg_left (by positivity) hmpos hm
    have h2 : 2 * p ^ (N + 2) / (p / 2) ^ (n + 1) = 2 ^ (n + 2) * p ^ (N - n + 1) := by
      calc 2 * p ^ (N + 2) / (p / 2) ^ (n + 1)
          = 2 * p ^ (N + 2) * ((p / 2) ^ (n + 1))⁻¹ := by rw [div_eq_mul_inv]
        _ = 2 * p ^ (N + 2) * ((2:ℝ) ^ (n + 1) / p ^ (n + 1)) := by
              rw [div_pow, inv_div]
        _ = (2 * 2 ^ (n + 1)) * (p ^ (N + 2) / p ^ (n + 1)) := by ring
        _ = 2 ^ (n + 2) * p ^ (N - n + 1) := by
              rw [show (2:ℝ) ^ (n + 2) = 2 * 2 ^ (n + 1) by
                    rw [show n + 2 = 1 + (n + 1) by omega, pow_add, pow_one],
                show p ^ (N + 2) / p ^ (n + 1) = p ^ (N - n + 1) by
                  rw [div_eq_mul_inv, ← pow_sub₀ p hp0ne (show n + 1 ≤ N + 2 by omega),
                    show N + 2 - (n + 1) = N - n + 1 by omega]]
    rw [h2] at h1
    exact h1
  calc N0 ≤ q * (q * T - S ^ 2) / S ^ 2 := hN0le
    _ ≤ q * (2 * eps * (m ^ 2 * p ^ (2 * N - 2)) + m * q ^ 2) / S ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (le_of_lt hqpos))
          (le_of_lt hSsqpos)
    _ ≤ q * (2 * eps * (m ^ 2 * p ^ (2 * N - 2)) + m * q ^ 2)
          / (m ^ 2 * p ^ (2 * N - 2) * (1/2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hSsq'
    _ = 4 * q * eps + 2 * q ^ 3 / (m * p ^ (2 * N - 2)) := by
        field_simp
        ring
    _ ≤ 4 * p ^ (N - n) + 2 * p ^ (N + 2) / m := by
        rw [show (4:ℝ) * q * eps = 4 * (q * eps) by ring,
          show (2:ℝ) * q ^ 3 / (m * p ^ (2 * N - 2)) = 2 * (q ^ 3 / (m * p ^ (2 * N - 2))) by ring,
          hqeps, hq3]
        exact le_of_eq (by ring)
    _ ≤ (2 ^ (n + 2) + 4) * p ^ (N - n + 1) := by nlinarith [hterm1, hterm2]

end Work.HP.badclass
