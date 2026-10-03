import Mathlib

namespace Work.FIArea7

/-- Arithmetic comparison for `S₂`: `Y^{3/2} ≤ 2^{3/2}N^{9/38}`, `N^{3/4+9/38} = N^{75/76}`,
`log(cN+2)^{BS2} ≤ 2^{BS2}log(N+2)^{Bf}`. -/
theorem t2psi_cmp_S2 (N c d : ℕ) (k : ℤ) (Y : ℕ) (KS2 BS2 Bf : ℝ)
    (hN : 2 ≤ N) (hc : 1 ≤ c) (hd : 1 ≤ d) (hY1 : 1 ≤ Y)
    (hYle : (Y : ℝ) ≤ 2 * (N : ℝ) ^ ((3:ℝ)/19))
    (hK : 0 < KS2) (hBS2 : 0 ≤ BS2) (hBf3 : 3 ≤ Bf) (hBf : BS2 ≤ Bf)
    (hlog : Real.log ((c : ℝ) * (N : ℝ) + 2) ≤ 2 * Real.log ((N : ℝ) + 2)) :
    KS2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4) * (Y : ℝ) ^ ((3:ℝ)/2)
        * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ BS2
      ≤ (KS2 * (2:ℝ) ^ ((3:ℝ)/2 + BS2)) * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
          * (N : ℝ) ^ ((75:ℝ)/76) * (Real.log ((N : ℝ) + 2)) ^ Bf := by
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hN0 : (0:ℝ) ≤ (N:ℝ) := le_of_lt hNpos
  have hc1 : (1:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  -- `log(N+2) ≥ 1` since `N + 2 ≥ 4 > e`.
  have hlog4 : (1:ℝ) ≤ Real.log 4 := by
    have h : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [h]; nlinarith [Real.log_two_gt_d9]
  have h1log : (1:ℝ) ≤ Real.log ((N:ℝ) + 2) := by
    have hle : Real.log (4:ℝ) ≤ Real.log ((N:ℝ)+2) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hcN2 : (2:ℝ) ≤ (c:ℝ)*(N:ℝ) := by
    have := mul_le_mul hc1 hN2 (by norm_num : (0:ℝ) ≤ 2) (by linarith : (0:ℝ) ≤ (c:ℝ))
    simpa using this
  have hlogc0 : (0:ℝ) ≤ Real.log ((c:ℝ)*(N:ℝ)+2) := Real.log_nonneg (by linarith)
  have hlogN0 : (0:ℝ) ≤ Real.log ((N:ℝ)+2) := Real.log_nonneg (by linarith)
  -- `log(cN+2)^{BS2} ≤ 2^{BS2} log(N+2)^{Bf}`.
  have hlogfinal : (Real.log ((c:ℝ)*(N:ℝ)+2))^BS2 ≤ (2:ℝ)^BS2 * (Real.log ((N:ℝ)+2))^Bf := by
    have hle : (Real.log ((c:ℝ)*(N:ℝ)+2))^BS2 ≤ (2:ℝ)^BS2 * (Real.log ((N:ℝ)+2))^BS2 := by
      have h := Real.rpow_le_rpow hlogc0 hlog hBS2
      rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hlogN0] at h
    have hmono : (Real.log ((N:ℝ)+2))^BS2 ≤ (Real.log ((N:ℝ)+2))^Bf :=
      Real.rpow_le_rpow_of_exponent_le h1log hBf
    calc (Real.log ((c:ℝ)*(N:ℝ)+2))^BS2
        ≤ (2:ℝ)^BS2 * (Real.log ((N:ℝ)+2))^BS2 := hle
      _ ≤ (2:ℝ)^BS2 * (Real.log ((N:ℝ)+2))^Bf :=
          mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)) BS2)
  -- `Y^{3/2} ≤ 2^{3/2} N^{9/38}`.
  have hYpow : (Y:ℝ)^((3:ℝ)/2) ≤ (2:ℝ)^((3:ℝ)/2) * (N:ℝ)^((9:ℝ)/38) := by
    have hYnn : (0:ℝ) ≤ (Y:ℝ) := by positivity
    have h1 : (Y:ℝ)^((3:ℝ)/2) ≤ (2 * (N:ℝ)^((3:ℝ)/19))^((3:ℝ)/2) :=
      Real.rpow_le_rpow hYnn hYle (by norm_num)
    have h2 : (2 * (N:ℝ)^((3:ℝ)/19))^((3:ℝ)/2)
        = (2:ℝ)^((3:ℝ)/2) * ((N:ℝ)^((3:ℝ)/19))^((3:ℝ)/2) :=
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0 ((3:ℝ)/19))
    have h3 : ((N:ℝ)^((3:ℝ)/19))^((3:ℝ)/2) = (N:ℝ)^((9:ℝ)/38) := by
      rw [← Real.rpow_mul hN0 ((3:ℝ)/19) ((3:ℝ)/2),
          show (3:ℝ)/19 * ((3:ℝ)/2) = (9:ℝ)/38 by norm_num]
    calc (Y:ℝ)^((3:ℝ)/2) ≤ (2 * (N:ℝ)^((3:ℝ)/19))^((3:ℝ)/2) := h1
      _ = (2:ℝ)^((3:ℝ)/2) * ((N:ℝ)^((3:ℝ)/19))^((3:ℝ)/2) := h2
      _ = (2:ℝ)^((3:ℝ)/2) * (N:ℝ)^((9:ℝ)/38) := by rw [h3]
  have hNadd : (N:ℝ)^((3:ℝ)/4) * (N:ℝ)^((9:ℝ)/38) = (N:ℝ)^((75:ℝ)/76) := by
    rw [← Real.rpow_add hNpos ((3:ℝ)/4) ((9:ℝ)/38),
        show (3:ℝ)/4 + (9:ℝ)/38 = (75:ℝ)/76 by norm_num]
  have hNY : (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/2) ≤ (2:ℝ)^((3:ℝ)/2) * (N:ℝ)^((75:ℝ)/76) := by
    have h1 := mul_le_mul_of_nonneg_left hYpow (Real.rpow_nonneg hN0 ((3:ℝ)/4))
    calc (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/2)
        ≤ (N:ℝ)^((3:ℝ)/4) * ((2:ℝ)^((3:ℝ)/2) * (N:ℝ)^((9:ℝ)/38)) := h1
      _ = (2:ℝ)^((3:ℝ)/2) * (N:ℝ)^((75:ℝ)/76) := by rw [← hNadd]; ring
  have h2add : (2:ℝ)^((3:ℝ)/2 + BS2) = (2:ℝ)^((3:ℝ)/2) * (2:ℝ)^BS2 :=
    Real.rpow_add (by norm_num) _ _
  have hcore : (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/2) * (Real.log ((c:ℝ)*(N:ℝ)+2))^BS2
      ≤ (2:ℝ)^((3:ℝ)/2 + BS2) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf := by
    have h1 := mul_le_mul hNY hlogfinal (Real.rpow_nonneg hlogc0 BS2)
        (mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((3:ℝ)/2))
                    (Real.rpow_nonneg hN0 ((75:ℝ)/76)))
    calc (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/2) * (Real.log ((c:ℝ)*(N:ℝ)+2))^BS2
        ≤ ((2:ℝ)^((3:ℝ)/2) * (N:ℝ)^((75:ℝ)/76)) * ((2:ℝ)^BS2 * (Real.log ((N:ℝ)+2))^Bf) := h1
      _ = (2:ℝ)^((3:ℝ)/2 + BS2) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf := by
          rw [h2add]; ring
  have hPpos : 0 < KS2 * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1) := by
    have hc0 : (0:ℝ) < (c:ℝ) := by linarith
    have hd0 : (0:ℝ) < (d:ℝ) := by
      have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      linarith
    have hk0 : (0:ℝ) < |(k:ℝ)| + 1 := by positivity
    positivity
  have hP : 0 ≤ KS2 * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1) := le_of_lt hPpos
  calc
    KS2 * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1) * (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/2)
        * (Real.log ((c:ℝ)*(N:ℝ)+2))^BS2
      = (KS2 * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1))
          * ((N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/2) * (Real.log ((c:ℝ)*(N:ℝ)+2))^BS2) := by ring
    _ ≤ (KS2 * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1))
          * ((2:ℝ)^((3:ℝ)/2 + BS2) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf) :=
        mul_le_mul_of_nonneg_left hcore hP
    _ = (KS2 * (2:ℝ)^((3:ℝ)/2 + BS2)) * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1)
          * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf := by ring

end Work.FIArea7
