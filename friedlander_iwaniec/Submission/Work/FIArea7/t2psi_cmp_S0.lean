import Mathlib

namespace Work.FIArea7

/-- Arithmetic comparison for `S₀`: `Y ≤ 2N^{3/19}`, `c^{1/8} ≤ c`, `log(Y+2) ≤ log(N+2)`,
`2N^{3/19} ≤ 4N^{75/76}` and `d, |k|+1 ≥ 1` give the stated bound. -/
theorem t2psi_cmp_S0 (N c d : ℕ) (k : ℤ) (Y : ℕ) (C8 Bf : ℝ)
    (hN : 2 ≤ N) (hc : 1 ≤ c) (hd : 1 ≤ d) (hY1 : 1 ≤ Y)
    (hYle : (Y : ℝ) ≤ 2 * (N : ℝ) ^ ((3:ℝ)/19)) (hYleN : (Y : ℝ) ≤ (N : ℝ))
    (hC8 : 0 < C8) (hBf : 3 ≤ Bf) :
    16 * C8 * (c : ℝ) ^ ((1:ℝ)/8) * (Y : ℝ) * (Real.log ((Y : ℝ) + 2)) ^ (3:ℕ)
      ≤ (128 * C8 + 64) * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76)
          * (Real.log ((N : ℝ) + 2)) ^ Bf := by
  have hC8nn : (0:ℝ) ≤ C8 := le_of_lt hC8
  have hcnn : (0:ℝ) ≤ (c:ℝ) := by positivity
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have : (1:ℕ) ≤ N := by omega
    exact_mod_cast this
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hYnn : (0:ℝ) ≤ (Y:ℝ) := by positivity
  have hlogYnn : 0 ≤ Real.log ((Y:ℝ) + 2) := by
    apply Real.log_nonneg
    have : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY1
    linarith
  have hlogNnn : 0 ≤ Real.log ((N:ℝ) + 2) := by
    apply Real.log_nonneg
    linarith
  have hlogNge1 : (1:ℝ) ≤ Real.log ((N:ℝ) + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith : (0:ℝ) < (N:ℝ)+2)]
    have h3 : (3:ℝ) ≤ (N:ℝ) + 2 := by linarith
    linarith [Real.exp_one_lt_three]
  have hY4 : (Y:ℝ) ≤ 4 * (N:ℝ)^((75:ℝ)/76) := by
    have h2 : (N:ℝ)^((3:ℝ)/19) ≤ (N:ℝ)^((75:ℝ)/76) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (3:ℝ)/19 ≤ (75:ℝ)/76)
    have h3 : 2 * (N:ℝ)^((3:ℝ)/19) ≤ 2 * (N:ℝ)^((75:ℝ)/76) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    have hN75nn : (0:ℝ) ≤ (N:ℝ)^((75:ℝ)/76) := Real.rpow_nonneg (le_of_lt hNpos) _
    have h4 : 2 * (N:ℝ)^((75:ℝ)/76) ≤ 4 * (N:ℝ)^((75:ℝ)/76) := by linarith
    linarith
  have hA : (c:ℝ)^((1:ℝ)/8) ≤ (c:ℝ) := by
    have hc1 : (1:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
    have := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num : (1:ℝ)/8 ≤ 1)
    simpa [Real.rpow_one] using this
  have hlog : (Real.log ((Y:ℝ)+2))^(3:ℕ) ≤ (Real.log ((N:ℝ)+2))^Bf := by
    have hle : (Y:ℝ)+2 ≤ (N:ℝ)+2 := by linarith
    have hlogmono : Real.log ((Y:ℝ)+2) ≤ Real.log ((N:ℝ)+2) :=
      Real.log_le_log (by linarith : (0:ℝ) < (Y:ℝ)+2) hle
    have hpow3 : (Real.log ((Y:ℝ)+2))^(3:ℕ) ≤ (Real.log ((N:ℝ)+2))^(3:ℕ) :=
      pow_le_pow_left₀ hlogYnn hlogmono 3
    have h3Bf : (Real.log ((N:ℝ)+2))^(3:ℕ) ≤ (Real.log ((N:ℝ)+2))^Bf := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hlogNge1 hBf
    linarith
  have hN75nn : (0:ℝ) ≤ (N:ℝ)^((75:ℝ)/76) := Real.rpow_nonneg (le_of_lt hNpos) _
  have hCY : 16 * C8 * (Y:ℝ) ≤ (128*C8+64) * (N:ℝ)^((75:ℝ)/76) := by
    calc 16 * C8 * (Y:ℝ)
        ≤ 16 * C8 * (4 * (N:ℝ)^((75:ℝ)/76)) :=
          mul_le_mul_of_nonneg_left hY4 (by linarith : (0:ℝ) ≤ 16 * C8)
      _ = 64 * C8 * (N:ℝ)^((75:ℝ)/76) := by ring
      _ ≤ (128*C8+64) * (N:ℝ)^((75:ℝ)/76) :=
          mul_le_mul_of_nonneg_right (by linarith : (64:ℝ)*C8 ≤ 128*C8+64) hN75nn
  have hQnn : (0:ℝ) ≤ (128*C8+64) * (N:ℝ)^((75:ℝ)/76) := by
    have : (0:ℝ) ≤ 128*C8+64 := by linarith
    exact mul_nonneg this hN75nn
  have hp : 16 * C8 * (Y:ℝ) * (Real.log ((Y:ℝ)+2))^(3:ℕ)
      ≤ (128*C8+64) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf :=
    mul_le_mul hCY hlog (pow_nonneg hlogYnn 3) hQnn
  have hPnn : (0:ℝ) ≤ 16 * C8 * (Y:ℝ) * (Real.log ((Y:ℝ)+2))^(3:ℕ) := by
    have h1 : (0:ℝ) ≤ 16 * C8 := by linarith
    exact mul_nonneg (mul_nonneg h1 hYnn) (pow_nonneg hlogYnn 3)
  have hkey : (c:ℝ)^((1:ℝ)/8) * (16 * C8 * (Y:ℝ) * (Real.log ((Y:ℝ)+2))^(3:ℕ))
      ≤ (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1) * ((128*C8+64) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf) := by
    have hQpart_nn : (0:ℝ) ≤ (128*C8+64) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf :=
      mul_nonneg hQnn (Real.rpow_nonneg hlogNnn Bf)
    have hstep1 : (c:ℝ)^((1:ℝ)/8) * (16 * C8 * (Y:ℝ) * (Real.log ((Y:ℝ)+2))^(3:ℕ))
        ≤ (c:ℝ) * ((128*C8+64) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf) :=
      mul_le_mul hA hp hPnn hcnn
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hk1 : (1:ℝ) ≤ |(k:ℝ)| + 1 := by
      have : (0:ℝ) ≤ |(k:ℝ)| := abs_nonneg _
      linarith
    have hdk : (1:ℝ) ≤ (d:ℝ) * (|(k:ℝ)|+1) := by
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ (d:ℝ) * (|(k:ℝ)|+1) := mul_le_mul hd1 hk1 (by norm_num) (by linarith)
    have hstep2 : (c:ℝ) * ((128*C8+64) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf)
        ≤ (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1) * ((128*C8+64) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf) := by
      have h1 : (c:ℝ) * 1 ≤ (c:ℝ) * ((d:ℝ) * (|(k:ℝ)|+1)) :=
        mul_le_mul_of_nonneg_left hdk hcnn
      rw [mul_one] at h1
      have h2 := mul_le_mul_of_nonneg_right h1 hQpart_nn
      simpa [mul_assoc] using h2
    linarith [hstep1, hstep2]
  calc
    16 * C8 * (c:ℝ)^((1:ℝ)/8) * (Y:ℝ) * (Real.log ((Y:ℝ)+2))^(3:ℕ)
        = (c:ℝ)^((1:ℝ)/8) * (16 * C8 * (Y:ℝ) * (Real.log ((Y:ℝ)+2))^(3:ℕ)) := by ring
      _ ≤ (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1) * ((128*C8+64) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf) := hkey
      _ = (128*C8+64) * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf := by ring

end Work.FIArea7
