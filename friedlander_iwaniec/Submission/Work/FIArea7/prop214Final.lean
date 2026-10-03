import Mathlib
import Submission.Work.FIArea7.Prop214Defs

namespace Work.FIArea7

/-- **FI, Proposition 21.4 (21.13), final arithmetic assembly.**  With
`R = truncR M N = ⌈√(MN)⌉ + 2`, `X = (M+N)^{1/12}`, `Y = (MN)^{11/12}`,
`L = log(MN+2)` and `W = L^A`:

`2·C·X·Y·W + 2·(C₁·log(2R))·C·X·Y·W + En ≤ (2C + 2(log 8 + 1/2)C₁C + 625C₁)·X·Y·L^{A+1}`.

The two logarithmic ingredients are `log(2R) ≤ (log 8 + 1/2)·log(MN+2)`
(from `2R ≤ 8√(MN)`) and `1 ≤ log(MN+2)` (from `MN ≥ 1`, so `MN + 2 ≥ 3 > e`). -/
theorem prop214Final (C A C1 En : ℝ) (hC : 0 < C) (hA : 0 < A) (hC1 : 0 < C1)
    (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hEn : En ≤ 625 * C1) :
    2 * (C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
          * (Real.log (M * N + 2)) ^ A)
      + 2 * (C1 * Real.log (2 * (Work.FIArea7.truncR M N : ℝ)))
          * (C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
              * (Real.log (M * N + 2)) ^ A)
      + En
      ≤ (2 * C + 2 * (Real.log 8 + 1 / 2) * C1 * C + 625 * C1)
          * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
          * (Real.log (M * N + 2)) ^ (A + 1) := by
  have hMN : 1 ≤ M * N := by nlinarith [hM, hN]
  have hMNpos : 0 < M * N := lt_of_lt_of_le one_pos hMN
  have hMpN : 1 ≤ M + N := by linarith
  have hMpNpos : 0 < M + N := by linarith
  set X : ℝ := (M + N) ^ ((1 : ℝ) / 12) with hXdef
  set Y : ℝ := (M * N) ^ ((11 : ℝ) / 12) with hYdef
  set L : ℝ := Real.log (M * N + 2) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    rw [Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < M * N + 2)]
    linarith [Real.exp_one_lt_three, hMN]
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hX1 : 1 ≤ X := by rw [hXdef]; exact Real.one_le_rpow hMpN (by norm_num)
  have hY1 : 1 ≤ Y := by rw [hYdef]; exact Real.one_le_rpow hMN (by norm_num)
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX1
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY1
  rw [Real.rpow_add hLpos, Real.rpow_one]
  set W : ℝ := L ^ A with hWdef
  have hW1 : 1 ≤ W := by rw [hWdef]; exact Real.one_le_rpow hL1 (le_of_lt hA)
  have hWpos : 0 < W := lt_of_lt_of_le one_pos hW1
  -- the size of the truncation radius: `2R ≤ 8√(MN)`
  have h2R : 2 * ((Work.FIArea7.truncR M N : ℕ) : ℝ) ≤ 8 * Real.sqrt (M * N) := by
    have hcast : ((Work.FIArea7.truncR M N : ℕ) : ℝ)
        = (Nat.ceil (Real.sqrt (M * N)) : ℝ) + 2 := by
      simp [Work.FIArea7.truncR]
    have hceil : (Nat.ceil (Real.sqrt (M * N)) : ℝ) < Real.sqrt (M * N) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg (M * N))
    have hsqrt1 : 1 ≤ Real.sqrt (M * N) := Real.one_le_sqrt.mpr hMN
    rw [hcast]; nlinarith [hceil, hsqrt1]
  have hRpos : 0 < ((Work.FIArea7.truncR M N : ℕ) : ℝ) := by
    have hcast : ((Work.FIArea7.truncR M N : ℕ) : ℝ)
        = (Nat.ceil (Real.sqrt (M * N)) : ℝ) + 2 := by
      simp [Work.FIArea7.truncR]
    have hceil : (Nat.ceil (Real.sqrt (M * N)) : ℝ) < Real.sqrt (M * N) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg (M * N))
    rw [hcast]; linarith [hceil, Real.sqrt_nonneg (M * N)]
  have hs_pos : 0 < Real.sqrt (M * N) := lt_of_lt_of_le one_pos (Real.one_le_sqrt.mpr hMN)
  -- the logarithmic gain
  have hlogR : Real.log (2 * ((Work.FIArea7.truncR M N : ℕ) : ℝ))
      ≤ (Real.log 8 + 1/2) * L := by
    have h1 : Real.log (2 * ((Work.FIArea7.truncR M N : ℕ) : ℝ))
        ≤ Real.log (8 * Real.sqrt (M * N)) :=
      Real.log_le_log (by linarith [hRpos]) h2R
    have h2 : Real.log (8 * Real.sqrt (M * N)) = Real.log 8 + Real.log (M * N) / 2 := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hs_pos), Real.log_sqrt (le_of_lt hMNpos)]
    rw [h2] at h1
    have h3 : Real.log (M * N) / 2 ≤ L / 2 := by
      have := Real.log_le_log hMNpos (by linarith : M * N ≤ M * N + 2)
      rw [hLdef]; linarith
    have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have h4 : Real.log 8 ≤ Real.log 8 * L := le_mul_of_one_le_right hlog8 hL1
    nlinarith [h1, h3, h4]
  -- the three pieces
  have h1 : 2 * (C * X * Y * W) ≤ 2 * (C * X * Y * W) * L := by
    have h0 : (0 : ℝ) ≤ 2 * (C * X * Y * W) := by positivity
    have := mul_le_mul_of_nonneg_left hL1 h0
    simpa using this
  have h2 : 2 * (C1 * Real.log (2 * ((Work.FIArea7.truncR M N : ℕ) : ℝ))) * (C * X * Y * W)
           ≤ 2 * (Real.log 8 + 1/2) * C1 * C * (X * Y * W * L) := by
    have h0 : (0 : ℝ) ≤ 2 * C1 * C * (X * Y * W) := by positivity
    have key := mul_le_mul_of_nonneg_left hlogR h0
    nlinarith [key]
  have hPL1 : 1 ≤ X * Y * W * L := by
    have hXY : 1 ≤ X * Y := by nlinarith [hX1, hY1]
    have hXYW : 1 ≤ X * Y * W := by nlinarith [hXY, hW1]
    nlinarith [hXYW, hL1]
  have h3 : En ≤ 625 * C1 * (X * Y * W * L) := by
    have h0 : (0 : ℝ) ≤ 625 * C1 := by positivity
    have key := le_mul_of_one_le_right h0 hPL1
    nlinarith [hEn, key]
  nlinarith [h1, h2, h3]

end Work.FIArea7
