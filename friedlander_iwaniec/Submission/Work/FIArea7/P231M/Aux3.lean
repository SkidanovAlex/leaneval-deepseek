import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7.P231M

noncomputable section

/-- The comparison of logs behind `finalArith`: `log(2(⌈√(MN)⌉+2)) ≤ (1+log 4)·log(MN+2)`. -/
lemma log_ceil_le {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    Real.log (2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ))
      ≤ (1 + Real.log 4) * Real.log (M * N + 2) := by
  have hMN1 : 1 ≤ M * N := by nlinarith
  have hceil : (((Nat.ceil (Real.sqrt (M * N)) : ℕ)) : ℝ) < Real.sqrt (M * N) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have harg0 : (0 : ℝ) < 2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) ≤ ((Nat.ceil (Real.sqrt (M * N)) : ℕ) : ℝ) := by positivity
    push_cast
    linarith
  have harg : 2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ)
      ≤ (M * N + 2) ^ (1 + Real.log 4) := by
    have hstep1 : 2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ) ≤ 4 * (M * N + 2) := by
      have h1 : ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ)
          = ((Nat.ceil (Real.sqrt (M * N)) : ℕ) : ℝ) + 2 := by push_cast; ring
      rw [h1]
      have hs : Real.sqrt (M * N) ≤ M * N := by
        nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ M * N), Real.sqrt_nonneg (M * N)]
      linarith
    have hstep2 : 4 * (M * N + 2) ≤ (M * N + 2) ^ (1 + Real.log 4) := by
      have hbase : (3 : ℝ) ≤ M * N + 2 := by linarith
      have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
        exact le_of_lt Real.exp_one_lt_three
      have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have h3pow : (4 : ℝ) ≤ (3 : ℝ) ^ (Real.log 4) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3) (Real.log 4)]
        calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num : (0 : ℝ) < 4)).symm
          _ ≤ Real.exp (Real.log 4 * Real.log 3) := Real.exp_le_exp.mpr (by nlinarith)
          _ = Real.exp (Real.log 3 * Real.log 4) := by rw [mul_comm]
      have hpow : (4 : ℝ) ≤ (M * N + 2) ^ (Real.log 4) :=
        le_trans h3pow (Real.rpow_le_rpow (by norm_num) hbase hlog4)
      have hbase0 : (0 : ℝ) < M * N + 2 := by linarith
      rw [Real.rpow_add hbase0 1 (Real.log 4), Real.rpow_one]
      calc (4 : ℝ) * (M * N + 2) = (M * N + 2) * 4 := by ring
        _ ≤ (M * N + 2) * (M * N + 2) ^ (Real.log 4) :=
            mul_le_mul_of_nonneg_left hpow (le_of_lt hbase0)
    linarith
  calc Real.log (2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ))
      ≤ Real.log ((M * N + 2) ^ (1 + Real.log 4)) := Real.log_le_log harg0 harg
    _ = (1 + Real.log 4) * Real.log (M * N + 2) := Real.log_rpow (by linarith) _

theorem finalArith {C A C1 S1 M N : ℝ} (hC : 0 < C) (hA : 0 < A) (hC1 : 0 < C1)
    (hS1 : 0 ≤ S1) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) * (Real.log (M * N + 2)) ^ A
      + (C1 / 2) * (Real.log (2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ))) ^ 4 * S1
          * (C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
              * (Real.log (M * N + 2)) ^ A)
      ≤ (C + (C1 / 2) * (1 + Real.log 4) ^ 4 * S1 * C)
          * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
          * (Real.log (M * N + 2)) ^ (A + 4) := by
  have hMN1 : 1 ≤ M * N := by nlinarith
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  have hL1 : (1 : ℝ) ≤ Real.log (M * N + 2) :=
    le_of_lt (hlog3.trans_le (Real.log_le_log (by norm_num) (by linarith)))
  have hL0 : (0 : ℝ) < Real.log (M * N + 2) := lt_of_lt_of_le one_pos hL1
  have hY := log_ceil_le hM hN
  have hYnn : (0 : ℝ) ≤ Real.log (2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ) := by
      have h2 : (0 : ℝ) ≤ ((Nat.ceil (Real.sqrt (M * N)) : ℕ) : ℝ) := by positivity
      push_cast
      linarith
    exact Real.log_nonneg (by linarith)
  have hY4 : (Real.log (2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ))) ^ 4
      ≤ (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4 := by
    calc (Real.log (2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ))) ^ 4
        ≤ ((1 + Real.log 4) * Real.log (M * N + 2)) ^ 4 := pow_le_pow_left₀ hYnn hY 4
      _ = (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4 := mul_pow _ _ 4
  have hL4 : (1 : ℝ) ≤ (Real.log (M * N + 2)) ^ 4 := one_le_pow₀ hL1
  have hkey : 1 + (C1 / 2) * S1
        * (Real.log (2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ))) ^ 4
      ≤ (1 + (C1 / 2) * (1 + Real.log 4) ^ 4 * S1) * (Real.log (M * N + 2)) ^ 4 := by
    have ha : (0 : ℝ) ≤ (C1 / 2) * S1 := by positivity
    have h1 : (C1 / 2) * S1 * (Real.log (2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ))) ^ 4
        ≤ (C1 / 2) * S1 * ((1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4) :=
      mul_le_mul_of_nonneg_left hY4 ha
    nlinarith [h1, hL4, ha]
  have hpowadd : (Real.log (M * N + 2)) ^ (A + 4)
      = (Real.log (M * N + 2)) ^ A * (Real.log (M * N + 2)) ^ 4 := by
    rw [Real.rpow_add hL0 A 4]
    congr 1
    exact Real.rpow_natCast (Real.log (M * N + 2)) 4
  have hmul := mul_le_mul_of_nonneg_left hkey
    (show (0 : ℝ) ≤ C * ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12))
        * (Real.log (M * N + 2)) ^ A by positivity)
  calc C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
        * (Real.log (M * N + 2)) ^ A
      + (C1 / 2) * (Real.log (2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ))) ^ 4 * S1
          * (C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
              * (Real.log (M * N + 2)) ^ A)
      = C * ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12))
          * (Real.log (M * N + 2)) ^ A
          * (1 + (C1 / 2) * S1
              * (Real.log (2 * ((Nat.ceil (Real.sqrt (M * N)) + 2 : ℕ) : ℝ))) ^ 4) := by ring
    _ ≤ C * ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12))
          * (Real.log (M * N + 2)) ^ A
          * ((1 + (C1 / 2) * (1 + Real.log 4) ^ 4 * S1)
              * (Real.log (M * N + 2)) ^ 4) := hmul
    _ = (C + (C1 / 2) * (1 + Real.log 4) ^ 4 * S1 * C)
          * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
          * (Real.log (M * N + 2)) ^ (A + 4) := by
        rw [hpowadd]
        ring

end

end Work.FIArea7.P231M
