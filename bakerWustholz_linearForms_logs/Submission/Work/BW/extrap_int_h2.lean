import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.num_xi
import Submission.Work.BW.num_blaschke_eta
import Submission.Work.BW.log_Y24_le
import Submission.Work.BW.extrap_int_h2_xi_facts
import Submission.Work.BW.extrap_int_h2_bounds_trim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

set_option maxHeartbeats 2000000 in
theorem extrap_int_h2 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (h : ℕ) (hh : 19 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (J : ℕ) (hJ : (J : ℝ) ≤ 50 * Real.log (2 * r * d))
    (j : ℕ) (hj : j + 2 ≤ r) (Sp : ℕ)
    (hSp : (Sp : ℝ) = ⌊2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)⌋₊)
    (Tp : ℕ)
    (hTp : (Tp : ℝ) = ⌊(1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r d σ : ℝ)⌋₊)
    (s : ℤ) (hss : ((|s| : ℤ) : ℝ) ≤ 2 ^ (j + 1) * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ ((2 * pxi r ^ r)⁻¹) ^ J / r)
    (hq3 : pxi r ^ (-((r * J : ℕ) : ℤ)) / pD r d σ ≤ q)
    (hI : 3.422 * 2 ^ j * (6.3 * pxi r ^ j + q) + 0.735 * pxi r ^ (j + r * J) + 1.133 +
        3.03 * 2 ^ j * ((2 * pxi r ^ r)⁻¹) ^ J + 0.044 * (J : ℝ) / Real.log (2 * r * d) - 9 * 2 ^ r ≤
        -2.2 * 2 ^ r) :
    (d : ℝ) * (h : ℝ) * pxi r ^ j * pxi r ^ (r * J) * (pT r d σ : ℝ) +
        (1.133 - 9 * 2 ^ r) * (pS r d h : ℝ) * pD r d σ +
        1.01 * (((Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * pD r d σ +
        0.044 * (J : ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ +
      ((Tp : ℝ) + 1) * Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1 / 3 : ℝ))⁻¹ ^ 2 * (Sp : ℝ) ^ 2 *
        Real.exp (2 * (Sp : ℝ)) * (max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ))) ^ (2 * (Sp : ℝ) + 1)) +
      Real.log ((2 * (Sp : ℝ) + 1) * ((Tp : ℝ) + 1)) < 0 := by
  obtain ⟨hSp608, hSp_le, hSp_le_q, hZ_le, hX_le, hTp_le, hTp1_le, hT0, hD0, hD608, hS0, hS608,
    hQ2q, hSD0, hSD608⟩ :=
      extrap_int_h2_bounds_trim hr hd h hh σ hσ J j hj Sp hSp Tp hTp s hss q hq1 hq3
  obtain ⟨hxi0, hxi1, hY1, hYE, hPE, hYB, hP0, hP1, hE0, hE1, hQ21, hQ2le, h2xir, hB1⟩ :=
      extrap_int_h2_xi_facts hr J j hj
  obtain ⟨hT1, hT2, hT3, hS608'⟩ := num_T hr hd hh σ hσ
  have hX1 : (1 : ℝ) ≤ max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ)) := le_max_left _ _
  have hlogY := log_Y24_le hSp608 hX1 hX_le Tp
  set Q2 : ℝ := (2 : ℝ) ^ j with hQ2
  set QJ : ℝ := (2 : ℝ) ^ J with hQJ
  set Pr2 : ℝ := (2 : ℝ) ^ (r - 2) with hPr2
  set Pr : ℝ := (2 : ℝ) ^ r with hPr
  set Pj : ℝ := pxi r ^ j with hPj
  set Ex : ℝ := pxi r ^ (r * J) with hEx
  set Yx : ℝ := pxi r ^ (-((r * J : ℕ) : ℤ)) with hYx
  set Bx : ℝ := ((2 * pxi r ^ r)⁻¹) ^ J with hBx
  set Sx : ℝ := (pS r d h : ℝ) with hSx
  set Dx : ℝ := pD r d σ with hDx
  set Tx : ℝ := (pT r d σ : ℝ) with hTx
  set sR : ℝ := (Sp : ℝ) with hsR
  set tR : ℝ := (Tp : ℝ) with htR
  set zz : ℝ := ((|s| : ℤ) : ℝ) with hzz
  set LL : ℝ := Real.log (2 * r * d) with hLL
  set XX : ℝ := max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ)) with hXX
  set LG : ℝ := Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1 / 3 : ℝ))⁻¹ ^ 2 * (Sp : ℝ) ^ 2 *
    Real.exp (2 * (Sp : ℝ)) * XX ^ (2 * (Sp : ℝ) + 1)) with hLG
  set LB : ℝ := Real.log ((2 * (Sp : ℝ) + 1) * ((Tp : ℝ) + 1)) with hLB
  set LTp : ℝ := Real.log ((Tp : ℝ) + 1) with hLTp
  have hQ20 : (0 : ℝ) < Q2 := by rw [hQ2]; positivity
  have hQJ0 : (0 : ℝ) < QJ := by rw [hQJ]; positivity
  have hPr2pos : (0 : ℝ) ≤ Pr2 := by linarith [hQ21, hQ2le]
  have hpow2 : Pr = Pr2 * 4 := by
    rw [hPr, hPr2, show r = (r - 2) + 2 by omega, pow_add]; norm_num
  have htR0 : (0 : ℝ) ≤ tR := by rw [htR]; positivity
  have hPr4 : (4 : ℝ) ≤ Pr := by
    rw [hPr]
    have hb : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
    norm_num at hb ⊢
    linarith [hb]
  have hB0 : (0 : ℝ) ≤ Bx := by
    rw [hBx]
    exact pow_nonneg (le_of_lt (inv_pos.mpr (by have h := pow_pos hxi0 r; linarith))) J
  have hDxle : Dx ≤ Sx * Dx := by
    have h1 : (1 : ℝ) ≤ Sx := by linarith [hS608]
    have h := mul_le_mul_of_nonneg_right h1 hD0.le
    simpa using h
  have hLTp_le : LTp ≤ 612 + Sx * Dx := by
    have h2 : LTp ≤ Real.log (7 * Dx) := by
      rw [hLTp]
      exact Real.log_le_log (by linarith [htR0]) hTp1_le
    have h3 : Real.log (7 * Dx) = Real.log 7 + Real.log Dx :=
      Real.log_mul (by norm_num) (ne_of_gt hD0)
    have h4 : Real.log 7 ≤ 6 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 by norm_num)
      linarith
    have h5 : Real.log Dx ≤ 606 + Dx / 608 := by
      have hL : Real.log 608 ≤ 607 := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 608 by norm_num)
        linarith
      have h := bw_log_le_of_log_le (a := 608) (t := Dx) (L := 607) (by norm_num) hD608 hL
      linarith
    linarith [h2, h3, h4, h5, hDxle]
  have hPE0 : (0 : ℝ) ≤ Pj * Ex := mul_nonneg hP0 hE0.le
  have hXY0 : (0 : ℝ) ≤ Q2 * Yx * Sx :=
    mul_nonneg (mul_nonneg (by linarith [hQ21]) (le_trans zero_le_one hY1)) hS0.le
  have hPES0 : (0 : ℝ) ≤ Q2 * Pj * Sx :=
    mul_nonneg (mul_nonneg (by linarith [hQ21]) hP0) hS0.le
  have hA : (d : ℝ) * (h : ℝ) * Pj * Ex * Tx ≤ 0.735 * Pj * Ex * Sx * Dx := by
    have hlt := mul_le_mul_of_nonneg_right hT3 hPE0
    linarith [hlt]
  have hsum : sR + zz ≤ 4 * sR := by linarith [hZ_le, hSp608]
  have hC : 1.01 * ((sR + zz) / QJ) * Dx ≤ 4.04 * Q2 * Bx * Sx * Dx := by
    have h1 : (sR + zz) / QJ ≤ (4 * sR) / QJ := div_le_div_of_nonneg_right hsum hQJ0.le
    have h2 : (4 * sR) / QJ ≤ (4 * (Q2 * Yx * Sx)) / QJ :=
      div_le_div_of_nonneg_right (by linarith [hSp_le]) hQJ0.le
    have h4 : (4 * (Q2 * Yx * Sx)) / QJ = 4 * Q2 * (Yx / QJ) * Sx := by ring
    have h3 : (sR + zz) / QJ ≤ 4 * Q2 * (Yx / QJ) * Sx := by linarith [h1, h2, h4]
    have ha : ((sR + zz) / QJ) * Dx ≤ (4 * Q2 * (Yx / QJ) * Sx) * Dx :=
      mul_le_mul_of_nonneg_right h3 hD0.le
    have hb : 1.01 * ((sR + zz) / QJ) * Dx ≤ 1.01 * ((4 * Q2 * (Yx / QJ) * Sx) * Dx) := by
      have h5 : 1.01 * ((sR + zz) / QJ) * Dx = 1.01 * (((sR + zz) / QJ) * Dx) := by ring
      rw [h5]
      exact mul_le_mul_of_nonneg_left ha (by norm_num)
    have hc : 1.01 * ((4 * Q2 * (Yx / QJ) * Sx) * Dx) = 4.04 * Q2 * Bx * Sx * Dx := by
      rw [hYB]; ring
    exact le_trans hb (le_of_eq hc)
  have hElog : (tR + 1) * LG + LB ≤ 3.48 * sR * (tR + 1) + (tR + 1) + LTp := by
    have h0 : (tR + 1) * (0.05 * sR + 1) = 0.05 * sR * (tR + 1) + (tR + 1) := by ring
    linarith [hlogY, h0]
  have hI' : 3.422 * Q2 * (6.3 * Pj + q) + 0.735 * (Pj * Ex) + 1.133 + 3.03 * Q2 * Bx
      + 0.044 * (J : ℝ) / LL - 9 * Pr ≤ -2.2 * Pr := by linarith [hI, hPE]
  have hSpq : sR ≤ Q2 * q * Dx * Sx := by
    have h0 : Q2 * (q * Dx) * Sx = Q2 * q * Dx * Sx := by ring
    linarith [hSp_le_q, h0]
  have hSpTp : sR * tR ≤ 6.3 * Q2 * Pj * Sx * Dx := by
    have h1 : sR * tR ≤ (Q2 * Yx * Sx) * ((1 - pxi r) * Pj * Ex * Tx) :=
      mul_le_mul hSp_le hTp_le htR0 hXY0
    have h2 : (Q2 * Yx * Sx) * ((1 - pxi r) * Pj * Ex * Tx)
        = Q2 * Pj * Sx * ((1 - pxi r) * Tx * (Yx * Ex)) := by ring
    have h3 : Q2 * Pj * Sx * ((1 - pxi r) * Tx * (Yx * Ex))
        = Q2 * Pj * Sx * ((1 - pxi r) * Tx) := by rw [hYE, mul_one]
    have h4 : Q2 * Pj * Sx * ((1 - pxi r) * Tx) ≤ Q2 * Pj * Sx * (6.3 * Dx) :=
      mul_le_mul_of_nonneg_left hT2 hPES0
    have h5 : Q2 * Pj * Sx * (6.3 * Dx) = 6.3 * Q2 * Pj * Sx * Dx := by ring
    linarith [h1, h2, h3, h4, h5]
  have hE3 : 3.48 * sR * (tR + 1) + (tR + 1) + LTp
      ≤ 3.48 * (6.3 * Q2 * Pj * Sx * Dx + Q2 * q * Dx * Sx) + 7 * Dx + 612 + Sx * Dx := by
    have h1 : 3.48 * sR * (tR + 1) ≤ 3.48 * (6.3 * Q2 * Pj * Sx * Dx + Q2 * q * Dx * Sx) := by
      have h6 : sR * (tR + 1) = sR * tR + sR := by ring
      have h7 : sR * tR + sR ≤ 6.3 * Q2 * Pj * Sx * Dx + Q2 * q * Dx * Sx := by
        linarith [hSpTp, hSpq]
      linarith [h6, h7]
    linarith [h1, hTp1_le, hLTp_le]
  have hHIm : (3.422 * Q2 * (6.3 * Pj + q) + 0.735 * (Pj * Ex) + 1.133 + 3.03 * Q2 * Bx
      + 0.044 * (J : ℝ) / LL - 9 * Pr) * (Sx * Dx) ≤ -2.2 * Pr * (Sx * Dx) :=
    mul_le_mul_of_nonneg_right hI' hSD0.le
  have hdef1 : 3.48 * 6.3 * Q2 * Pj * Sx * Dx ≤ 3.422 * 6.3 * Q2 * Pj * Sx * Dx
      + 0.3654 * (Pr / 4) * (Sx * Dx) := by
    have h1 : Pr2 = Pr / 4 := by linarith [hpow2]
    have hP2 : Q2 * Pj ≤ Pr / 4 := by
      have h0 := mul_le_mul hQ2le hP1 hP0 hPr2pos
      linarith [h0, h1]
    have h4 : (Q2 * Pj) * (Sx * Dx) ≤ (Pr / 4) * (Sx * Dx) :=
      mul_le_mul_of_nonneg_right hP2 hSD0.le
    have h5 : (Q2 * Pj) * (Sx * Dx) = Q2 * Pj * Sx * Dx := by ring
    linarith [h4, h5]
  have hdef2 : 3.48 * Q2 * q * Dx * Sx ≤ 3.422 * Q2 * q * Dx * Sx + 0.058 * (Pr / 4) * (Sx * Dx) := by
    have h1 : Pr2 = Pr / 4 := by linarith [hpow2]
    have h2 : Q2 * q ≤ Pr / 4 := by linarith [hQ2q, h1]
    have h4 : (Q2 * q) * (Sx * Dx) ≤ (Pr / 4) * (Sx * Dx) :=
      mul_le_mul_of_nonneg_right h2 hSD0.le
    have h5 : (Q2 * q) * (Sx * Dx) = Q2 * q * Dx * Sx := by ring
    linarith [h4, h5]
  have hdefB : 4.04 * Q2 * Bx * Sx * Dx ≤ 3.03 * Q2 * Bx * Sx * Dx + 1.01 * (Pr / 4) * (Sx * Dx) := by
    have h1 : Pr2 = Pr / 4 := by linarith [hpow2]
    have h2 : Q2 * Bx ≤ Pr / 4 := by
      have h0 := mul_le_mul hQ2le hB1 hB0 hPr2pos
      linarith [h0, h1]
    have h4 : (Q2 * Bx) * (Sx * Dx) ≤ (Pr / 4) * (Sx * Dx) :=
      mul_le_mul_of_nonneg_right h2 hSD0.le
    have h5 : (Q2 * Bx) * (Sx * Dx) = Q2 * Bx * Sx * Dx := by ring
    linarith [h4, h5]
  have h7D : 7 * Dx ≤ 7 * (Sx * Dx) / 608 := by
    have h1 : Dx ≤ Sx * Dx / 608 := by
      have h2 : (608 : ℝ) * Dx ≤ Sx * Dx := mul_le_mul_of_nonneg_right hS608 hD0.le
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 608)]
      linarith [h2]
    linarith [h1]
  have hfinal : (d : ℝ) * (h : ℝ) * Pj * Ex * Tx + (1.133 - 9 * Pr) * Sx * Dx
      + 1.01 * ((sR + zz) / QJ) * Dx + 0.044 * (J : ℝ) / LL * Sx * Dx + (tR + 1) * LG + LB
      ≤ -2.2 * Pr * (Sx * Dx) + 1.4334 * (Pr / 4) * (Sx * Dx) + 7 * (Sx * Dx) / 608
        + 612 + Sx * Dx := by
    linarith [hA, hC, hElog, hE3, hHIm, hdef1, hdef2, hdefB, h7D]
  have hPrSD : 4 * (Sx * Dx) ≤ Pr * (Sx * Dx) := mul_le_mul_of_nonneg_right hPr4 hSD0.le
  linarith [hfinal, hPrSD, hSD608]

end Work.BW
