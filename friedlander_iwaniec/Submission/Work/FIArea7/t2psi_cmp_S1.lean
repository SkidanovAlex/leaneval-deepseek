import Mathlib

namespace Work.FIArea7

/-- Arithmetic comparison for `S₁`: `Y^{3/4} ≤ 2^{3/4}N^{9/76}`, `N^{3/4+9/76} = N^{66/76} ≤ N^{75/76}`,
`log(cN+2)^{Blow} ≤ 2^{Blow}log(N+2)^{Bf}` (using `N ≥ 2` so that `log(N+2) > 1`). -/
theorem t2psi_cmp_S1 (N c d : ℕ) (k : ℤ) (Y : ℕ) (Klow Blow Bf : ℝ)
    (hN : 2 ≤ N) (hc : 1 ≤ c) (hd : 1 ≤ d) (hY1 : 1 ≤ Y)
    (hYle : (Y : ℝ) ≤ 2 * (N : ℝ) ^ ((3:ℝ)/19))
    (hK : 0 < Klow) (hBlow : 0 ≤ Blow) (hBf3 : 3 ≤ Bf) (hBf : Blow ≤ Bf)
    (hlog : Real.log ((c : ℝ) * (N : ℝ) + 2) ≤ 2 * Real.log ((N : ℝ) + 2)) :
    Klow * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4) * (Y : ℝ) ^ ((3:ℝ)/4)
        * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ Blow
      ≤ (Klow * (2:ℝ) ^ ((3:ℝ)/4 + Blow)) * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
          * (N : ℝ) ^ ((75:ℝ)/76) * (Real.log ((N : ℝ) + 2)) ^ Bf := by
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by linarith
  have hYpos : (0:ℝ) < (Y:ℝ) := by
    have : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY1
    linarith
  have hc1 : (1:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  -- `log(N+2) > 1`, since `N+2 ≥ 4` and `log 4 = 2 log 2 > 1`.
  have h4 : (4:ℝ) ≤ (N:ℝ) + 2 := by linarith
  have hlog4le : Real.log 4 ≤ Real.log ((N:ℝ) + 2) := Real.log_le_log (by norm_num) h4
  have hlog4ge1 : (1:ℝ) ≤ Real.log 4 := by
    have hh : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [hh]; nlinarith [Real.log_two_gt_d9]
  have hLn1 : (1:ℝ) ≤ Real.log ((N:ℝ)+2) := le_trans hlog4ge1 hlog4le
  have hLn0 : (0:ℝ) ≤ Real.log ((N:ℝ)+2) := le_trans zero_le_one hLn1
  have hcN1 : (1:ℝ) ≤ (c:ℝ)*(N:ℝ)+2 := by nlinarith [hc1, hN1]
  have hLc0 : (0:ℝ) ≤ Real.log ((c:ℝ)*(N:ℝ)+2) := Real.log_nonneg hcN1
  -- The core inequality with the common factor `Klow·c·d·(|k|+1)` removed.
  have hcore : (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/4) * (Real.log ((c:ℝ)*(N:ℝ)+2))^Blow
      ≤ (2:ℝ)^((3:ℝ)/4 + Blow) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf := by
    -- `Y^{3/4} ≤ (2N^{3/19})^{3/4} = 2^{3/4} N^{9/76}`
    have hy2 : (Y:ℝ)^((3:ℝ)/4) ≤ (2:ℝ)^((3:ℝ)/4) * (N:ℝ)^((9:ℝ)/76) := by
      have h1 : (Y:ℝ)^((3:ℝ)/4) ≤ (2 * (N:ℝ)^((3:ℝ)/19))^((3:ℝ)/4) :=
        Real.rpow_le_rpow (le_of_lt hYpos) hYle (by norm_num)
      have h2 : (2 * (N:ℝ)^((3:ℝ)/19))^((3:ℝ)/4) = (2:ℝ)^((3:ℝ)/4) * (N:ℝ)^((9:ℝ)/76) := by
        have hexp : (3:ℝ)/19 * ((3:ℝ)/4) = (9:ℝ)/76 := by norm_num
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (le_of_lt hNpos), hexp]
      rw [h2] at h1
      exact h1
    have hpiece1 : (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/4)
        ≤ (2:ℝ)^((3:ℝ)/4) * (N:ℝ)^((75:ℝ)/76) := by
      calc (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/4)
          ≤ (N:ℝ)^((3:ℝ)/4) * ((2:ℝ)^((3:ℝ)/4) * (N:ℝ)^((9:ℝ)/76)) :=
            mul_le_mul_of_nonneg_left hy2 (by positivity)
        _ = (2:ℝ)^((3:ℝ)/4) * (N:ℝ)^((3:ℝ)/4 + (9:ℝ)/76) := by
            rw [show (N:ℝ)^((3:ℝ)/4) * ((2:ℝ)^((3:ℝ)/4) * (N:ℝ)^((9:ℝ)/76))
                  = (2:ℝ)^((3:ℝ)/4) * ((N:ℝ)^((3:ℝ)/4) * (N:ℝ)^((9:ℝ)/76)) by ring,
                ← Real.rpow_add hNpos]
        _ ≤ (2:ℝ)^((3:ℝ)/4) * (N:ℝ)^((75:ℝ)/76) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    -- `log(cN+2)^{Blow} ≤ (2 log(N+2))^{Blow} ≤ 2^{Blow} log(N+2)^{Bf}`
    have hpiece2 : (Real.log ((c:ℝ)*(N:ℝ)+2))^Blow ≤ (2:ℝ)^Blow * (Real.log ((N:ℝ)+2))^Bf := by
      calc (Real.log ((c:ℝ)*(N:ℝ)+2))^Blow
          ≤ (2 * Real.log ((N:ℝ)+2))^Blow := Real.rpow_le_rpow hLc0 hlog hBlow
        _ = (2:ℝ)^Blow * (Real.log ((N:ℝ)+2))^Blow := Real.mul_rpow (by norm_num) hLn0
        _ ≤ (2:ℝ)^Blow * (Real.log ((N:ℝ)+2))^Bf :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hLn1 hBf) (by positivity)
    calc (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/4) * (Real.log ((c:ℝ)*(N:ℝ)+2))^Blow
        ≤ ((2:ℝ)^((3:ℝ)/4) * (N:ℝ)^((75:ℝ)/76)) * ((2:ℝ)^Blow * (Real.log ((N:ℝ)+2))^Bf) :=
          mul_le_mul hpiece1 hpiece2 (by positivity) (by positivity)
      _ = (2:ℝ)^((3:ℝ)/4 + Blow) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf := by
          rw [show ((2:ℝ)^((3:ℝ)/4) * (N:ℝ)^((75:ℝ)/76)) * ((2:ℝ)^Blow * (Real.log ((N:ℝ)+2))^Bf)
                = ((2:ℝ)^((3:ℝ)/4) * (2:ℝ)^Blow) * ((N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf) by ring,
              ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          ring
  -- Multiply the core inequality by the nonnegative common factor.
  have hP : 0 ≤ Klow * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1) := by positivity
  calc Klow * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1) * (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/4)
          * (Real.log ((c:ℝ)*(N:ℝ)+2))^Blow
      = (Klow * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1))
          * ((N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/4) * (Real.log ((c:ℝ)*(N:ℝ)+2))^Blow) := by ring
    _ ≤ (Klow * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1))
          * ((2:ℝ)^((3:ℝ)/4 + Blow) * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf) :=
        mul_le_mul_of_nonneg_left hcore hP
    _ = (Klow * (2:ℝ)^((3:ℝ)/4 + Blow)) * (c:ℝ) * (d:ℝ) * (|(k:ℝ)|+1)
          * (N:ℝ)^((75:ℝ)/76) * (Real.log ((N:ℝ)+2))^Bf := by ring

end Work.FIArea7
