import Mathlib

namespace Work.HP.MDEstimates

/-- The elementary arithmetic estimate `m ≤ (9 / log 2) * 2 ^ (m / 9)` for every natural `m`,
proved from `t ≤ exp t` applied to `t = (m/9) * log 2`. -/
theorem nat_le_coeff_mul_rpow (m : ℕ) :
    (m : ℝ) ≤ (9 / Real.log 2) * (2:ℝ) ^ ((m:ℝ)/9) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hkey : ((m:ℝ)/9) * Real.log 2 ≤ (2:ℝ) ^ ((m:ℝ)/9) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    have h := Real.add_one_le_exp (Real.log 2 * ((m:ℝ)/9))
    nlinarith [h]
  have h1 : (m:ℝ) * Real.log 2 ≤ 9 * (2:ℝ) ^ ((m:ℝ)/9) := by
    have h := mul_le_mul_of_nonneg_left hkey (by norm_num : (0:ℝ) ≤ 9)
    nlinarith [h]
  have h2 : (m:ℝ) ≤ (9 * (2:ℝ) ^ ((m:ℝ)/9)) / Real.log 2 := (le_div_iff₀ hlog2).mpr h1
  calc (m:ℝ) ≤ (9 * (2:ℝ) ^ ((m:ℝ)/9)) / Real.log 2 := h2
    _ = (9 / Real.log 2) * (2:ℝ) ^ ((m:ℝ)/9) := by ring

/-- For `x ≥ 1`, `2 ^ (⌈logb 2 x⌉₊ - 1) ≤ x`. -/
theorem two_rpow_pred_le (x : ℝ) (hx : 1 ≤ x) :
    (2:ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℝ) - 1) ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hlog0 : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hx
  have hlt : (⌈Real.logb 2 x⌉₊ : ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one hlog0
  have h2 : (2:ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ) < 2 * x := by
    calc (2:ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ) < 2 ^ (Real.logb 2 x + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hlt
      _ = 2 * x := by
          rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),
              Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) hx0,
              Real.rpow_one]
          ring
  have hsplit : (2:ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℝ) - 1) * (2:ℝ)^(1:ℝ)
      = (2:ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2) ((⌈Real.logb 2 x⌉₊ : ℝ) - 1) (1:ℝ),
        show ((⌈Real.logb 2 x⌉₊ : ℝ) - 1) + (1:ℝ) = (⌈Real.logb 2 x⌉₊ : ℝ) by ring]
  have h2b : (2:ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℝ) - 1) * (2:ℝ)^(1:ℝ) < 2 * x := by
    rw [hsplit]; exact h2
  rw [Real.rpow_one] at h2b
  nlinarith [h2b]

/-- The arithmetic estimate `(m+2)^3 ≤ (9/log 2 + 2)^3 * 2 ^ (m/3)`. -/
theorem ceil_logb_arith_aux (m : ℕ) :
    ((m : ℝ) + 2) ^ 3 ≤ (9 / Real.log 2 + 2) ^ 3 * (2:ℝ) ^ ((m:ℝ)/3) := by
  have hm : (m:ℝ) ≤ (9 / Real.log 2) * (2:ℝ) ^ ((m:ℝ)/9) := nat_le_coeff_mul_rpow m
  have hone : (1:ℝ) ≤ (2:ℝ) ^ ((m:ℝ)/9) :=
    Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) (by positivity)
  have hbound : (m:ℝ) + 2 ≤ (9 / Real.log 2 + 2) * (2:ℝ) ^ ((m:ℝ)/9) := by
    nlinarith [hm, hone]
  have hstep : ((m:ℝ)+2)^3 ≤ ((9 / Real.log 2 + 2) * (2:ℝ) ^ ((m:ℝ)/9))^3 :=
    pow_le_pow_left₀ (by positivity) hbound 3
  have hexp3 : ((m:ℝ)/9) * ((3:ℕ):ℝ) = (m:ℝ)/3 := by push_cast; ring
  have hrw : ((2:ℝ) ^ ((m:ℝ)/9)) ^ 3 = (2:ℝ) ^ ((m:ℝ)/3) := by
    rw [← Real.rpow_natCast ((2:ℝ) ^ ((m:ℝ)/9)) 3]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) ((m:ℝ)/9) ((3:ℕ):ℝ)]
    rw [hexp3]
  calc ((m:ℝ)+2)^3 ≤ ((9 / Real.log 2 + 2) * (2:ℝ) ^ ((m:ℝ)/9))^3 := hstep
    _ = (9 / Real.log 2 + 2)^3 * (2:ℝ) ^ ((m:ℝ)/3) := by rw [mul_pow, hrw]

/-- For `x ≥ 1`, `2 ^ (⌈logb 2 x⌉₊ / 3 - 1/3) ≤ x ^ (1/3)`. -/
theorem ceil_logb_lower_rpow_aux (x : ℝ) (hx : 1 ≤ x) :
    (2:ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℝ)/3 - 1/3) ≤ x ^ ((1:ℝ)/3) := by
  have hle : (2:ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℝ) - 1) ≤ x := two_rpow_pred_le x hx
  have hbase : (0:ℝ) ≤ (2:ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℝ) - 1) :=
    Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _
  have h3 : ((2:ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℝ) - 1)) ^ ((1:ℝ)/3) ≤ x ^ ((1:ℝ)/3) :=
    Real.rpow_le_rpow hbase hle (by norm_num : (0:ℝ) ≤ (1:ℝ)/3)
  have hexp : ((⌈Real.logb 2 x⌉₊ : ℝ) - 1) * ((1:ℝ)/3) = (⌈Real.logb 2 x⌉₊ : ℝ)/3 - 1/3 := by
    ring
  have hEq : ((2:ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℝ) - 1)) ^ ((1:ℝ)/3)
      = (2:ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℝ)/3 - 1/3) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) ((⌈Real.logb 2 x⌉₊ : ℝ) - 1) ((1:ℝ)/3)]
    rw [hexp]
  rwa [hEq] at h3

theorem ceil_logb_cube_le (x : ℝ) (hx : 1 ≤ x) :
    ((⌈Real.logb 2 x⌉₊ : ℝ) + 1) ^ 3 ≤ (9 / Real.log 2 + 2)^3 * x ^ ((1:ℝ)/3) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  set n := ⌈Real.logb 2 x⌉₊ with hn
  by_cases h0 : n = 0
  · rw [h0]
    have hC : (1:ℝ) ≤ (9 / Real.log 2 + 2)^3 := by
      have h1 : (1:ℝ) ≤ 9 / Real.log 2 + 2 := by
        have : 0 < 9 / Real.log 2 := by positivity
        linarith
      calc (1:ℝ) = 1^3 := by norm_num
        _ ≤ (9 / Real.log 2 + 2)^3 := pow_le_pow_left₀ (by norm_num) h1 3
    have hx13 : (1:ℝ) ≤ x ^ ((1:ℝ)/3) := Real.one_le_rpow hx (by norm_num : (0:ℝ) ≤ (1:ℝ)/3)
    have hmul : (1:ℝ) * 1 ≤ (9 / Real.log 2 + 2)^3 * x ^ ((1:ℝ)/3) :=
      mul_le_mul hC hx13 (by norm_num) (le_trans (by norm_num : (0:ℝ) ≤ 1) hC)
    simpa using hmul
  · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
    set m := n - 1 with hm
    have hmn : (m : ℝ) = (n : ℝ) - 1 := by
      rw [hm, Nat.cast_sub hn1, Nat.cast_one]
    have hA := ceil_logb_arith_aux m
    have hB := ceil_logb_lower_rpow_aux x hx
    have he1 : (n : ℝ) + 1 = (m : ℝ) + 2 := by rw [hmn]; ring
    have hexp2 : (m:ℝ)/3 = (n:ℝ)/3 - 1/3 := by rw [hmn]; ring
    have he2 : (2:ℝ)^((m:ℝ)/3) = (2:ℝ)^((n:ℝ)/3 - 1/3) := by rw [hexp2]
    have hCnn : (0:ℝ) ≤ (9 / Real.log 2 + 2)^3 := by
      apply pow_nonneg
      have : 0 < 9 / Real.log 2 := by positivity
      linarith
    calc ((n:ℝ)+1)^3 = ((m:ℝ)+2)^3 := by rw [he1]
      _ ≤ (9 / Real.log 2 + 2)^3 * (2:ℝ)^((m:ℝ)/3) := hA
      _ = (9 / Real.log 2 + 2)^3 * (2:ℝ)^((n:ℝ)/3 - 1/3) := by rw [he2]
      _ ≤ (9 / Real.log 2 + 2)^3 * x ^ ((1:ℝ)/3) :=
            mul_le_mul_of_nonneg_left hB hCnn

end Work.HP.MDEstimates
