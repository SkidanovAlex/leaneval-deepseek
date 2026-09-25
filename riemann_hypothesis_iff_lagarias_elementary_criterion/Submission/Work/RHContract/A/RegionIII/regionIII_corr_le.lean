import Mathlib
import Submission.Work.RHContract.A.RegionIII.caRegionIIIDefs

namespace Work.RHContract.A.RegionIII

noncomputable section

/-- `ξ ≥ 10^8` gives `L = log ξ ≥ 1/2 · 17`... auxiliary: `((10:ℝ)^8)^{−3/4} = 1/1000000`. -/
lemma ten_pow_eight_rpow_neg_three_quarters :
    ((10 : ℝ) ^ 8) ^ (-(3 / 4 : ℝ)) = 1 / 1000000 := by
  rw [← Real.rpow_natCast (10 : ℝ) 8]
  rw [← Real.rpow_mul (x := (10 : ℝ)) (by norm_num) ((8 : ℕ) : ℝ) (-(3 / 4 : ℝ))]
  norm_num

/-- `((10:ℝ)^8)^{−3/2} = 1/1000000000000`. -/
lemma ten_pow_eight_rpow_neg_three_halves :
    ((10 : ℝ) ^ 8) ^ (-(3 / 2 : ℝ)) = 1 / 1000000000000 := by
  rw [← Real.rpow_natCast (10 : ℝ) 8]
  rw [← Real.rpow_mul (x := (10 : ℝ)) (by norm_num) ((8 : ℕ) : ℝ) (-(3 / 2 : ℝ))]
  norm_num

/-- `((10:ℝ)^8)^{−1} = 1/100000000`. -/
lemma ten_pow_eight_rpow_neg_one :
    ((10 : ℝ) ^ 8) ^ (-(1 : ℝ)) = 1 / 100000000 := by
  rw [← Real.rpow_natCast (10 : ℝ) 8]
  rw [← Real.rpow_mul (x := (10 : ℝ)) (by norm_num) ((8 : ℕ) : ℝ) (-(1 : ℝ))]
  norm_num

/-- **Numeric core of the Region III Abel-correction estimate.**

For `ξ ≥ 10^8`, `L = log ξ`, `n ≥ ⌊√(2.5 ξ)⌋₊ + 1` and `Q = √ξ · L / log n`, and
`Θ − n ≤ 0.45 n^{3/4} + 2`, the sum of the five correction terms, after multiplication
by `√ξ · L`, is at most `0.181`. -/
theorem regionIII_corr_core (ξ n Q Θ : ℝ) (hξ8 : (10 : ℝ) ^ 8 ≤ ξ)
    (hn_pos : 0 < n) (hn15812 : (15812 : ℝ) ≤ n)
    (hQ0 : 0 ≤ Q) (hQ_le : Q ≤ 1.265 * n)
    (hΘn : Θ - n ≤ 0.45 * n ^ (3 / 4 : ℝ) + 2) :
    (0.45 * ξ ^ (-(3 / 4 : ℝ)) + 2 * ξ ^ (-(3 / 2 : ℝ)) + 3 * ξ ^ (-(1 : ℝ)))
      + (Θ - n) * Q / n ^ 2 + 0.76 * Q / n ^ (5 / 4 : ℝ) + 2 * Q / n ^ 2
      + 4.25 * Q / n ^ (3 / 2 : ℝ) ≤ 0.181 := by
  have hA : ξ ^ (-(3/4:ℝ)) ≤ 1/1000000 := by
    calc ξ ^ (-(3/4:ℝ)) ≤ ((10:ℝ)^8)^(-(3/4:ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hξ8 (by norm_num)
      _ = 1/1000000 := ten_pow_eight_rpow_neg_three_quarters
  have hB : ξ ^ (-(3/2:ℝ)) ≤ 1/1000000000000 := by
    calc ξ ^ (-(3/2:ℝ)) ≤ ((10:ℝ)^8)^(-(3/2:ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hξ8 (by norm_num)
      _ = 1/1000000000000 := ten_pow_eight_rpow_neg_three_halves
  have hC : ξ ^ (-(1:ℝ)) ≤ 1/100000000 := by
    calc ξ ^ (-(1:ℝ)) ≤ ((10:ℝ)^8)^(-(1:ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hξ8 (by norm_num)
      _ = 1/100000000 := ten_pow_eight_rpow_neg_one
  have h1 : 0.45 * ξ ^ (-(3 / 4 : ℝ)) + 2 * ξ ^ (-(3 / 2 : ℝ)) + 3 * ξ ^ (-(1 : ℝ))
      ≤ 1/1000000 := by
    have eA := mul_le_mul_of_nonneg_left hA (by norm_num : (0:ℝ) ≤ 0.45)
    have eB := mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 2)
    have eC := mul_le_mul_of_nonneg_left hC (by norm_num : (0:ℝ) ≤ 3)
    linarith [eA, eB, eC]
  have h2 : (Θ - n) * Q / n ^ 2 ≤ 1.265 * (0.45 * n ^ (-(1/4:ℝ)) + 2 * n ^ (-(1:ℝ))) := by
    have hkey1 : n^(3/4:ℝ) * n^(-(1:ℝ)) = n^(-(1/4:ℝ)) := by rw [← Real.rpow_add hn_pos]; norm_num
    have hnn : n/n^2 = n^(-(1:ℝ)) := by
      rw [← Real.rpow_natCast n 2]; nth_rewrite 1 [← Real.rpow_one n]
      rw [← Real.rpow_sub hn_pos]; norm_num
    have step1 : (Θ - n)*Q/n^2 ≤ (0.45*n^(3/4:ℝ)+2)*Q/n^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hΘn hQ0) (by positivity)
    have step2 : (0.45*n^(3/4:ℝ)+2)*Q/n^2 ≤ (0.45*n^(3/4:ℝ)+2)*(1.265*n)/n^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQ_le (by positivity)) (by positivity)
    have heq : (0.45*n^(3/4:ℝ)+2)*(1.265*n)/n^2
        = 1.265*(0.45*n^(-(1/4:ℝ)) + 2*n^(-(1:ℝ))) := by
      rw [show (0.45*n^(3/4:ℝ)+2)*(1.265*n)/n^2
          = 1.265*((0.45*n^(3/4:ℝ)+2)*(n/n^2)) by ring]
      rw [hnn]
      rw [show (0.45*n^(3/4:ℝ)+2)*n^(-(1:ℝ))
          = 0.45*(n^(3/4:ℝ)*n^(-(1:ℝ))) + 2*n^(-(1:ℝ)) by ring]
      rw [hkey1]
    linarith [step1, step2, heq]
  have h3 : 0.76 * Q / n ^ (5/4:ℝ) ≤ 0.76 * 1.265 * n ^ (-(1/4:ℝ)) := by
    have hQn : Q / n ^ (5/4:ℝ) ≤ 1.265*n^(-(1/4:ℝ)) := by
      have h0 : Q / n ^ (5/4:ℝ) ≤ (1.265*n)/n^(5/4:ℝ) :=
        div_le_div_of_nonneg_right hQ_le (Real.rpow_pos_of_pos hn_pos _).le
      have h2 : (1.265*n)/n^(5/4:ℝ) = 1.265*n^(-(1/4:ℝ)) := by
        rw [show (1.265:ℝ)*n/n^(5/4:ℝ) = 1.265*(n/n^(5/4:ℝ)) by ring]
        nth_rewrite 1 [← Real.rpow_one n]; rw [← Real.rpow_sub hn_pos]; norm_num
      rwa [h2] at h0
    calc 0.76 * Q / n ^ (5/4:ℝ) = 0.76 * (Q / n^(5/4:ℝ)) := by ring
      _ ≤ 0.76 * (1.265 * n^(-(1/4:ℝ))) := mul_le_mul_of_nonneg_left hQn (by norm_num)
      _ = 0.76 * 1.265 * n^(-(1/4:ℝ)) := by ring
  have h4 : 2 * Q / n ^ 2 ≤ 2 * 1.265 * n ^ (-(1:ℝ)) := by
    have hQn : Q / n ^ 2 ≤ 1.265*n^(-(1:ℝ)) := by
      have h0 : Q / n^2 ≤ (1.265*n)/n^2 := div_le_div_of_nonneg_right hQ_le (by positivity)
      have h2 : (1.265*n)/n^2 = 1.265*n^(-(1:ℝ)) := by
        rw [show (1.265:ℝ)*n/n^2 = 1.265*(n/n^2) by ring]
        rw [← Real.rpow_natCast n 2]; nth_rewrite 1 [← Real.rpow_one n]
        rw [← Real.rpow_sub hn_pos]; norm_num
      rwa [h2] at h0
    calc 2 * Q / n ^ 2 = 2 * (Q/n^2) := by ring
      _ ≤ 2 * (1.265 * n^(-(1:ℝ))) := mul_le_mul_of_nonneg_left hQn (by norm_num)
      _ = 2 * 1.265 * n^(-(1:ℝ)) := by ring
  have h5 : 4.25 * Q / n ^ (3/2:ℝ) ≤ 4.25 * 1.265 * n ^ (-(1/2:ℝ)) := by
    have hQn : Q / n ^ (3/2:ℝ) ≤ 1.265*n^(-(1/2:ℝ)) := by
      have h0 : Q / n ^ (3/2:ℝ) ≤ (1.265*n)/n^(3/2:ℝ) :=
        div_le_div_of_nonneg_right hQ_le (Real.rpow_pos_of_pos hn_pos _).le
      have h2 : (1.265*n)/n^(3/2:ℝ) = 1.265*n^(-(1/2:ℝ)) := by
        rw [show (1.265:ℝ)*n/n^(3/2:ℝ) = 1.265*(n/n^(3/2:ℝ)) by ring]
        nth_rewrite 1 [← Real.rpow_one n]; rw [← Real.rpow_sub hn_pos]; norm_num
      rwa [h2] at h0
    calc 4.25 * Q / n ^ (3/2:ℝ) = 4.25 * (Q / n^(3/2:ℝ)) := by ring
      _ ≤ 4.25 * (1.265 * n^(-(1/2:ℝ))) := mul_le_mul_of_nonneg_left hQn (by norm_num)
      _ = 4.25 * 1.265 * n^(-(1/2:ℝ)) := by ring
  have hnq : n ^ (-(1/4:ℝ)) ≤ 0.08918 := by
    have hb1 : ((15812:ℝ)^(-(1:ℝ)))^(1/4:ℝ) = (15812:ℝ)^(-(1/4:ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 15812)]; norm_num
    have hb2 : ((0.08918:ℝ)^(4:ℝ))^(1/4:ℝ) = (0.08918:ℝ) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 0.08918)]; norm_num
    have hbase : (15812:ℝ)^(-(1:ℝ)) ≤ (0.08918:ℝ)^(4:ℝ) := by rw [Real.rpow_neg_one]; norm_num
    have h15812 : (15812:ℝ)^(-(1/4:ℝ)) ≤ 0.08918 := by
      have hh := (Real.rpow_le_rpow_iff (by positivity : (0:ℝ) ≤ (15812:ℝ)^(-(1:ℝ)))
        (by positivity : (0:ℝ) ≤ (0.08918:ℝ)^(4:ℝ)) (by norm_num : (0:ℝ) < (1/4:ℝ))).mpr hbase
      rwa [hb1, hb2] at hh
    exact le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num) hn15812 (by norm_num)) h15812
  have hnh : n ^ (-(1/2:ℝ)) ≤ 0.008 := by
    have hb1 : ((15812:ℝ)^(-(1:ℝ)))^(1/2:ℝ) = (15812:ℝ)^(-(1/2:ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 15812)]; norm_num
    have hb2 : ((0.008:ℝ)^(2:ℝ))^(1/2:ℝ) = (0.008:ℝ) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 0.008)]; norm_num
    have hbase : (15812:ℝ)^(-(1:ℝ)) ≤ (0.008:ℝ)^(2:ℝ) := by rw [Real.rpow_neg_one]; norm_num
    have h15812 : (15812:ℝ)^(-(1/2:ℝ)) ≤ 0.008 := by
      have hh := (Real.rpow_le_rpow_iff (by positivity : (0:ℝ) ≤ (15812:ℝ)^(-(1:ℝ)))
        (by positivity : (0:ℝ) ≤ (0.008:ℝ)^(2:ℝ)) (by norm_num : (0:ℝ) < (1/2:ℝ))).mpr hbase
      rwa [hb1, hb2] at hh
    exact le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num) hn15812 (by norm_num)) h15812
  have hnl : n ^ (-(1:ℝ)) ≤ 0.0000633 := by
    have h1 : n ^ (-(1:ℝ)) ≤ (15812:ℝ)^(-(1:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hn15812 (by norm_num)
    have h2 : (15812:ℝ)^(-(1:ℝ)) = 1/15812 := by rw [Real.rpow_neg_one, one_div]
    rw [h2] at h1
    have : (1:ℝ)/15812 ≤ 0.0000633 := by norm_num
    linarith
  linarith [h1, h2, h3, h4, h5, hnq, hnh, hnl]

theorem regionIII_corr_le (ε : ℝ) (hξ : (10 : ℝ) ^ 8 ≤ Work.RHContract.A.RegionIII.caXiR ε) (Θ : ℝ)
    (hΘ : Θ ≤ (Work.RHContract.A.RegionIII.caN ε : ℝ) + (0.45 * (Work.RHContract.A.RegionIII.caN ε : ℝ) ^ (3 / 4 : ℝ) + 2)) :
    ((0.45 * Work.RHContract.A.RegionIII.caXiR ε ^ (3 / 4 : ℝ) + 2 + 3 * Real.sqrt (Work.RHContract.A.RegionIII.caXiR ε))
          / (Work.RHContract.A.RegionIII.caXiR ε ^ 2 * Work.RHContract.A.RegionIII.caL ε)
        + (Θ - (Work.RHContract.A.RegionIII.caN ε : ℝ)) / ((Work.RHContract.A.RegionIII.caN ε : ℝ) ^ 2 * Real.log (Work.RHContract.A.RegionIII.caN ε))
        + 0.76 / ((Work.RHContract.A.RegionIII.caN ε : ℝ) ^ (5 / 4 : ℝ) * Real.log (Work.RHContract.A.RegionIII.caN ε))
        + 2 / ((Work.RHContract.A.RegionIII.caN ε : ℝ) ^ 2 * Real.log (Work.RHContract.A.RegionIII.caN ε))
        + 4.25 / ((Work.RHContract.A.RegionIII.caN ε : ℝ) ^ (3 / 2 : ℝ) * Real.log (Work.RHContract.A.RegionIII.caN ε)))
      * (Real.sqrt (Work.RHContract.A.RegionIII.caXiR ε) * Work.RHContract.A.RegionIII.caL ε) ≤ 0.181 := by
  set ξ : ℝ := Work.RHContract.A.RegionIII.caXiR ε with hξdef
  set L : ℝ := Work.RHContract.A.RegionIII.caL ε with hLdef
  set n : ℝ := (Work.RHContract.A.RegionIII.caN ε : ℝ) with hndef
  set A1 : ℝ := (0.45 * ξ ^ (3 / 4 : ℝ) + 2 + 3 * Real.sqrt ξ) / (ξ ^ 2 * L) with hA1
  set A2 : ℝ := (Θ - n) / (n ^ 2 * Real.log n) with hA2
  set A3 : ℝ := 0.76 / (n ^ (5 / 4 : ℝ) * Real.log n) with hA3
  set A4 : ℝ := 2 / (n ^ 2 * Real.log n) with hA4
  set A5 : ℝ := 4.25 / (n ^ (3 / 2 : ℝ) * Real.log n) with hA5
  show (A1 + A2 + A3 + A4 + A5) * (Real.sqrt ξ * L) ≤ 0.181
  have hL_eq : L = Real.log ξ := by simp only [hLdef, caL, hξdef]
  have hξ8 : (10 : ℝ) ^ 8 ≤ ξ := by rw [hξdef]; exact hξ
  have hξ0 : 0 < ξ := by norm_num at hξ8; linarith
  have hLpos : 0 < L := by rw [hL_eq]; exact Real.log_pos (by linarith)
  have hL0 : L ≠ 0 := ne_of_gt hLpos
  have hn_eq : n = (Nat.floor (Real.sqrt (2.5 * ξ)) : ℝ) + 1 := by
    rw [hndef]
    simp only [caN]
    rw [← hξdef]
    push_cast
    ring
  have hn_ge : Real.sqrt (2.5 * ξ) ≤ n := by
    have h1 : (Nat.floor (Real.sqrt (2.5 * ξ)) : ℝ) ≤ Real.sqrt (2.5 * ξ) :=
      Nat.floor_le (by positivity)
    have h2 : Real.sqrt (2.5 * ξ) < (Nat.floor (Real.sqrt (2.5 * ξ)) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [hn_eq]; linarith
  have hξs : (10000 : ℝ) ≤ Real.sqrt ξ := by
    rw [Real.le_sqrt (by norm_num) hξ0.le]
    have : ((10000 : ℝ)) ^ 2 = 10 ^ 8 := by norm_num
    rw [this]; exact hξ8
  have hsqrt25 : (15811.3 : ℝ) ≤ Real.sqrt (2.5 * ξ) := by
    have hm : Real.sqrt (2.5 * ξ) = Real.sqrt 2.5 * Real.sqrt ξ := Real.sqrt_mul (by norm_num) ξ
    rw [hm]
    have hs25 : (1.58113 : ℝ) ≤ Real.sqrt 2.5 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    calc (15811.3 : ℝ) ≤ 1.58113 * 10000 := by norm_num
      _ ≤ Real.sqrt 2.5 * Real.sqrt ξ := mul_le_mul hs25 hξs (by norm_num) (by positivity)
  have hn_num : (15812 : ℝ) ≤ n := by
    have hfl : (15811 : ℕ) ≤ Nat.floor (Real.sqrt (2.5 * ξ)) :=
      Nat.le_floor (by linarith [hsqrt25])
    rw [hn_eq]
    exact_mod_cast (by omega : (15812 : ℕ) ≤ Nat.floor (Real.sqrt (2.5 * ξ)) + 1)
  have hn_pos : 0 < n := by linarith
  have hn0 : n ≠ 0 := ne_of_gt hn_pos
  have hlogn_ge : (L + 0.9) / 2 ≤ Real.log n := by
    have h1 : Real.log (Real.sqrt (2.5 * ξ)) ≤ Real.log n :=
      Real.log_le_log (Real.sqrt_pos.mpr (by positivity)) hn_ge
    rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) (ne_of_gt hξ0)] at h1
    have hlog25 : (0.9 : ℝ) ≤ Real.log 2.5 := by
      have he : Real.log (2.5 : ℝ) = Real.log 5 - Real.log 2 := by
        rw [show (2.5 : ℝ) = 5 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
      linarith [Real.log_five_gt_d9, Real.log_two_lt_d9, he]
    rw [hL_eq]
    linarith
  have hlogn_pos : 0 < Real.log n := by linarith [hlogn_ge, hLpos]
  have hlogn0 : Real.log n ≠ 0 := ne_of_gt hlogn_pos
  have hn5 : n ^ (5 / 4 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn_pos _)
  have hn3 : n ^ (3 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn_pos _)
  have hsqrt_le : Real.sqrt ξ ≤ n / 1.58113 := by
    have h2 : Real.sqrt (2.5 * ξ) = Real.sqrt 2.5 * Real.sqrt ξ := Real.sqrt_mul (by norm_num) ξ
    have hs25 : (1.58113 : ℝ) ≤ Real.sqrt 2.5 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have h3 : 1.58113 * Real.sqrt ξ ≤ Real.sqrt (2.5 * ξ) := by
      rw [h2]; exact mul_le_mul_of_nonneg_right hs25 (Real.sqrt_nonneg ξ)
    have h4 : 1.58113 * Real.sqrt ξ ≤ n := le_trans h3 hn_ge
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1.58113)]
    linarith
  have hratio : L / Real.log n ≤ 2 := by
    rw [div_le_iff₀ hlogn_pos]
    linarith [hlogn_ge, hLpos]
  have hQ_le : Real.sqrt ξ * L / Real.log n ≤ 1.265 * n := by
    rw [show Real.sqrt ξ * L / Real.log n = Real.sqrt ξ * (L / Real.log n) by ring]
    calc Real.sqrt ξ * (L / Real.log n) ≤ (n / 1.58113) * 2 :=
          mul_le_mul hsqrt_le hratio (by positivity) (by positivity)
      _ = (2 / 1.58113) * n := by ring
      _ ≤ 1.265 * n := mul_le_mul_of_nonneg_right (by norm_num) hn_pos.le
  have hsum : (A1 + A2 + A3 + A4 + A5) * (Real.sqrt ξ * L)
      = A1 * (Real.sqrt ξ * L) + A2 * (Real.sqrt ξ * L) + A3 * (Real.sqrt ξ * L)
        + A4 * (Real.sqrt ξ * L) + A5 * (Real.sqrt ξ * L) := by ring
  rw [hsum]
  have e1 : A1 * (Real.sqrt ξ * L)
      = 0.45 * ξ ^ (-(3 / 4 : ℝ)) + 2 * ξ ^ (-(3 / 2 : ℝ)) + 3 * ξ ^ (-(1 : ℝ)) := by
    rw [hA1, Real.sqrt_eq_rpow]
    have h35 : ξ ^ (3 / 4 : ℝ) * ξ ^ (1 / 2 : ℝ) = ξ ^ (5 / 4 : ℝ) := by
      rw [← Real.rpow_add hξ0]; norm_num
    have h5m : ξ ^ (5 / 4 : ℝ) / ξ ^ 2 = ξ ^ (-(3 / 4) : ℝ) := by
      rw [← Real.rpow_natCast ξ 2, ← Real.rpow_sub hξ0]; norm_num
    have h1m : ξ ^ (1 / 2 : ℝ) / ξ ^ 2 = ξ ^ (-(3 / 2) : ℝ) := by
      rw [← Real.rpow_natCast ξ 2, ← Real.rpow_sub hξ0]; norm_num
    have h11 : ξ ^ (1 / 2 : ℝ) * ξ ^ (1 / 2 : ℝ) = ξ := by
      rw [← Real.rpow_add hξ0]; norm_num
    have h2m : ξ / ξ ^ 2 = ξ ^ (-(1) : ℝ) := by
      rw [Real.rpow_neg_one]; field_simp
    have hstep : (0.45 * ξ ^ (3 / 4 : ℝ) + 2 + 3 * ξ ^ (1 / 2 : ℝ)) / (ξ ^ 2 * L)
          * (ξ ^ (1 / 2 : ℝ) * L)
        = 0.45 * (ξ ^ (3 / 4 : ℝ) * ξ ^ (1 / 2 : ℝ) / ξ ^ 2) + 2 * (ξ ^ (1 / 2 : ℝ) / ξ ^ 2)
          + 3 * (ξ ^ (1 / 2 : ℝ) * ξ ^ (1 / 2 : ℝ) / ξ ^ 2) := by
      field_simp
    rw [hstep, h35, h5m, h1m, h11, h2m]
  rw [e1]
  have e2 : A2 * (Real.sqrt ξ * L)
      = (Θ - n) * (Real.sqrt ξ * L / Real.log n) / n ^ 2 := by
    rw [hA2]; field_simp
  rw [e2]
  have e3 : A3 * (Real.sqrt ξ * L)
      = 0.76 * (Real.sqrt ξ * L / Real.log n) / n ^ (5 / 4 : ℝ) := by
    rw [hA3]; field_simp
  rw [e3]
  have e4 : A4 * (Real.sqrt ξ * L)
      = 2 * (Real.sqrt ξ * L / Real.log n) / n ^ 2 := by
    rw [hA4]; field_simp
  rw [e4]
  have e5 : A5 * (Real.sqrt ξ * L)
      = 4.25 * (Real.sqrt ξ * L / Real.log n) / n ^ (3 / 2 : ℝ) := by
    rw [hA5]; field_simp
  rw [e5]
  set Q : ℝ := Real.sqrt ξ * L / Real.log n with hQdef
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg ξ) hLpos.le) hlogn_pos.le
  have hΘn : Θ - n ≤ 0.45 * n ^ (3 / 4 : ℝ) + 2 := by linarith [hΘ]
  exact regionIII_corr_core ξ n Q Θ hξ8 hn_pos hn_num hQ0 hQ_le hΘn

end

end Work.RHContract.A.RegionIII
