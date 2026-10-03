import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarWDefs

namespace Work.FIArea4.Vflip.Vfd

theorem farB_absorptionZ (ε : ℝ) (hε : 0 < ε) (Clog : ℝ) (hClogpos : 0 < Clog)
    (hClog : ∀ x : ℝ, 1 ≤ x → Real.log (2 * x) + 1 ≤ Clog * x ^ (ε / 4)) :
    ∀ (R S D : ℕ) (H : ℝ) (L₀ : ℝ),
      1 ≤ R → 1 ≤ S → 1 ≤ D → 1 ≤ H → L₀ = Real.log (2 * (R : ℝ)) + 1 →
      L₀ * (4 * Real.sqrt 5 * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
            + ((R : ℝ) * (S : ℝ)) ^ (ε / 4)
              * (32 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)
                  + (Real.log (160 * H) + 1)
                    * (4 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                        + 2 * (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ))))
        ≤ (12 + 64 * Clog + 8 * (Real.log 80 + 1) * Clog)
          * ((Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ 2
                * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
              + (Real.log (2 * H) + 1) ^ 2 * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)
                  * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / (D : ℝ)
                      + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                      + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))) := by
  intro R S D H L₀ hR hS hD hH hL0
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  set P : ℝ := ((D:ℝ)*H*(R:ℝ)*(S:ℝ)) ^ ((1:ℝ)/2) with hP
  set T : ℝ := ((R:ℝ)*(S:ℝ)) ^ ((3:ℝ)/2) with hT
  set W : ℝ := ((R:ℝ)*(S:ℝ)) ^ (ε/2) with hW
  set B : ℝ := ((R:ℝ)*(S:ℝ)) ^ (ε/4) with hB
  set X2 : ℝ := 4*(R:ℝ)*(S:ℝ)^((3:ℝ)/4) + 2*(2*(R:ℝ))^((3:ℝ)/4)*(S:ℝ) with hX2def
  set X : ℝ := (R:ℝ)*(S:ℝ)^((3:ℝ)/4) with hX
  set Y : ℝ := (S:ℝ)*(R:ℝ)^((3:ℝ)/4) with hY
  set ZH : ℝ := Real.log (160*H) + 1 with hZH
  set logA : ℝ := Real.log (2*(R:ℝ)*(S:ℝ)) + 1 with hlogA
  set logH : ℝ := Real.log (2*H) + 1 with hlogH
  set M : ℝ := 12 + 64*Clog + 8*(Real.log 80 + 1)*Clog with hM
  have hRSnn : (0:ℝ) ≤ (R:ℝ)*(S:ℝ) := by positivity
  have hPnn : 0 ≤ P := by
    rw [hP]; apply Real.rpow_nonneg
    have hH0 : (0:ℝ) ≤ H := by linarith only [hH]
    positivity
  have hTnn : 0 ≤ T := by rw [hT]; exact Real.rpow_nonneg hRSnn _
  have hWnn : 0 ≤ W := by rw [hW]; exact Real.rpow_nonneg hRSnn _
  have hBnn : 0 ≤ B := by rw [hB]; exact Real.rpow_nonneg hRSnn _
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hYnn : 0 ≤ Y := by rw [hY]; positivity
  have hX2nn : 0 ≤ X2 := by rw [hX2def]; positivity
  have hZHnn : 0 ≤ ZH := by
    rw [hZH]
    have h : (0:ℝ) ≤ Real.log (160*H) := Real.log_nonneg (by linarith only [hH])
    linarith only [h]
  have hlogH1 : (1:ℝ) ≤ logH := by
    rw [hlogH]
    have h : (0:ℝ) ≤ Real.log (2*H) := Real.log_nonneg (by linarith only [hH])
    linarith only [h]
  have hlogH0 : (0:ℝ) ≤ logH := by linarith only [hlogH1]
  have hlogHsq1 : (1:ℝ) ≤ logH^2 := by
    have ha : (0:ℝ) ≤ logH - 1 := by linarith only [hlogH1]
    have hb : (0:ℝ) ≤ logH + 1 := by linarith only [hlogH1]
    nlinarith only [mul_nonneg ha hb]
  have hlog80 : (0:ℝ) ≤ Real.log 80 := Real.log_nonneg (by norm_num)
  have h80pos : (0:ℝ) ≤ Real.log 80 + 1 := by linarith only [hlog80]
  have hterm : (0:ℝ) ≤ 8*(Real.log 80 + 1)*Clog := by
    exact mul_nonneg (by linarith only [hlog80]) (le_of_lt hClogpos)
  have hMnn : (0:ℝ) ≤ M := by rw [hM]; nlinarith only [hterm, hClogpos]
  have hMge12 : (12:ℝ) ≤ M := by rw [hM]; nlinarith only [hterm, hClogpos]
  have hMge64 : (64:ℝ)*Clog ≤ M := by rw [hM]; nlinarith only [hterm, hClogpos]
  have hMge8 : 8*(Real.log 80 + 1)*Clog ≤ M := by rw [hM]; nlinarith only [hClogpos]
  have hL0_le_Clog : L₀ ≤ Clog * (R:ℝ)^(ε/4) := by
    have h := hClog (R:ℝ) hR1
    rw [hL0]; exact h
  have hBpow : (R:ℝ)^(ε/4) * B ≤ W := by
    rw [hB, hW]
    have hRpos : (0:ℝ) < (R:ℝ) := by linarith only [hR1]
    have hRle : (R:ℝ) ≤ (R:ℝ)*(S:ℝ) := by nlinarith only [hR1, hS1, hRpos]
    have hε4 : (0:ℝ) ≤ ε/4 := by linarith only [hε]
    have hp : (R:ℝ)^(ε/4) ≤ ((R:ℝ)*(S:ℝ))^(ε/4) := Real.rpow_le_rpow (le_of_lt hRpos) hRle hε4
    have hm := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hRSnn (ε/4))
    have hRSpos : (0:ℝ) < (R:ℝ)*(S:ℝ) := by positivity
    have hsq : ((R:ℝ)*(S:ℝ))^(ε/4) * ((R:ℝ)*(S:ℝ))^(ε/4) = ((R:ℝ)*(S:ℝ))^(ε/2) := by
      rw [← Real.rpow_add hRSpos (ε/4) (ε/4)]
      congr 1
      ring
    exact le_trans hm (le_of_eq hsq)
  have hLB : L₀ * B ≤ Clog * W := by
    have ha := mul_le_mul_of_nonneg_right hL0_le_Clog hBnn
    have hb : (Clog * (R:ℝ)^(ε/4)) * B ≤ Clog * W := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hBpow (le_of_lt hClogpos)
    linarith only [ha, hb]
  -- the first bracket term
  have h1 : L₀ * (4 * Real.sqrt 5 * P) ≤ M * (logA ^ 2 * P) := by
    have hlogAlog : Real.log (2*(R:ℝ)) ≤ Real.log (2*(R:ℝ)*(S:ℝ)) := by
      apply Real.log_le_log
      · positivity
      · nlinarith only [hR1, hS1]
    have hL0_le_logA : L₀ ≤ logA := by
      rw [hL0, hlogA]
      exact add_le_add hlogAlog le_rfl
    have hlogA1 : (1:ℝ) ≤ logA := by
      rw [hlogA]
      have hlog0 : (0:ℝ) ≤ Real.log (2*(R:ℝ)*(S:ℝ)) := Real.log_nonneg (by nlinarith only [hR1, hS1])
      linarith only [hlog0]
    have hlogAsq : logA ≤ logA^2 := by
      nlinarith only [hlogA1, sq_nonneg (logA - 1),
        mul_nonneg (by linarith only [hlogA1] : (0:ℝ) ≤ logA)
          (by linarith only [hlogA1] : (0:ℝ) ≤ logA - 1)]
    have hL0_le_logA2 : L₀ ≤ logA^2 := le_trans hL0_le_logA hlogAsq
    have hs5 : Real.sqrt 5 < 3 := by
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 3)]
      norm_num
    have h4s5 : 4 * Real.sqrt 5 ≤ 12 := by nlinarith only [hs5, Real.sqrt_nonneg 5]
    have hMge4s5 : 4 * Real.sqrt 5 ≤ M := by linarith only [h4s5, hMge12]
    have hcore : L₀ * (4 * Real.sqrt 5) ≤ M * logA^2 := by
      have hm := mul_le_mul hL0_le_logA2 hMge4s5 (by linarith only [Real.sqrt_nonneg 5]) (sq_nonneg logA)
      linarith only [hm]
    have hmul := mul_le_mul_of_nonneg_right hcore hPnn
    nlinarith only [hmul]
  -- the second bracket term
  have h2 : L₀ * (B * (32 * Real.sqrt 2 * T / (D:ℝ))) ≤ M * (logH ^ 2 * W * (T / (D:ℝ))) := by
    have hs2 : (32:ℝ)*Real.sqrt 2 ≤ 64 := by
      have h : Real.sqrt 2 < 2 := by
        rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
        norm_num
      nlinarith only [h, Real.sqrt_nonneg 2]
    have hC32 : Clog * (32*Real.sqrt 2) ≤ M * logH^2 := by
      have a1 : Clog * (32*Real.sqrt 2) ≤ Clog*64 := mul_le_mul_of_nonneg_left hs2 (le_of_lt hClogpos)
      have b1 : Clog*64 ≤ M := by linarith only [hMge64]
      have b2 : M ≤ M*logH^2 := by
        have hb := mul_le_mul_of_nonneg_left hlogHsq1 hMnn
        linarith only [hb]
      linarith only [a1, b1, b2]
    have hcore2 : L₀ * B * (32*Real.sqrt 2) ≤ M * logH^2 * W := by
      have h32nn : (0:ℝ) ≤ 32*Real.sqrt 2 := by positivity
      have ha := mul_le_mul_of_nonneg_right hLB h32nn
      have hb := mul_le_mul_of_nonneg_right hC32 hWnn
      linarith only [ha, hb]
    have hTd : (0:ℝ) ≤ T / (D:ℝ) := by
      have hDpos : (0:ℝ) < (D:ℝ) := by linarith only [hD1]
      positivity
    have hm := mul_le_mul_of_nonneg_right hcore2 hTd
    calc L₀ * (B * (32 * Real.sqrt 2 * T / (D:ℝ)))
        = (L₀ * B * (32*Real.sqrt 2)) * (T/(D:ℝ)) := by ring
      _ ≤ (M * logH^2 * W) * (T/(D:ℝ)) := hm
      _ = M * (logH ^ 2 * W * (T / (D:ℝ))) := by ring
  -- the third bracket term
  have h3 : L₀ * (B * (ZH * X2)) ≤ M * (logH ^ 2 * W * (X + Y)) := by
    have hZHle : ZH ≤ (Real.log 80 + 1) * logH := by
      rw [hZH, hlogH]
      have he : (160:ℝ)*H = 80*(2*H) := by ring
      rw [he, Real.log_mul (by norm_num : (80:ℝ) ≠ 0) (by linarith only [hH] : (2*H) ≠ 0)]
      have h2H : (0:ℝ) ≤ Real.log (2*H) := Real.log_nonneg (by linarith only [hH])
      nlinarith only [hlog80, h2H, mul_nonneg hlog80 h2H]
    have hX2le : X2 ≤ 4 * (X + Y) := by
      rw [hX2def, hX, hY]
      have hRpos : (0:ℝ) < (R:ℝ) := by linarith only [hR1]
      have hmr : (2*↑R)^((3:ℝ)/4) = (2:ℝ)^((3:ℝ)/4) * ↑R^((3:ℝ)/4) :=
        Real.mul_rpow (by norm_num) (le_of_lt hRpos)
      rw [hmr]
      have hp2 : (2:ℝ)^((3:ℝ)/4) ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (3:ℝ)/4 ≤ 1)
        simpa using h
      have hp : (2:ℝ)^((3:ℝ)/4) * ↑R^((3:ℝ)/4) ≤ 2 * ↑R^((3:ℝ)/4) :=
        mul_le_mul_of_nonneg_right hp2 (by positivity)
      have h2 : 2 * ((2:ℝ)^((3:ℝ)/4) * ↑R^((3:ℝ)/4)) * ↑S ≤ 2 * (2 * ↑R^((3:ℝ)/4)) * ↑S := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hp (by norm_num)
      nlinarith only [h2]
    have hML : 8*(Real.log 80 + 1)*Clog ≤ M*logH := by
      have h1 : M ≤ M*logH := by
        have hb := mul_le_mul_of_nonneg_left hlogH1 hMnn
        linarith only [hb]
      linarith only [hMge8, h1]
    have hC3 : Clog * (Real.log 80 + 1) * logH * 4 ≤ M * logH^2 := by
      have h4 : 4*Clog*(Real.log 80 + 1) ≤ M*logH := by
        have ht : 4*Clog*(Real.log 80 + 1) ≤ 8*(Real.log 80 + 1)*Clog := by
          nlinarith only [hlog80, hClogpos]
        linarith only [ht, hML]
      have h5 := mul_le_mul_of_nonneg_right h4 hlogH0
      nlinarith only [h5]
    have hXYnn : (0:ℝ) ≤ X + Y := by linarith only [hXnn, hYnn]
    have hClogWnn : (0:ℝ) ≤ Clog * W := mul_nonneg (le_of_lt hClogpos) hWnn
    have h80logHnn : (0:ℝ) ≤ (Real.log 80 + 1) * logH := mul_nonneg h80pos hlogH0
    have hstep1 : L₀ * B * ZH ≤ Clog * W * ((Real.log 80 + 1) * logH) := by
      have hh := mul_le_mul hLB hZHle hZHnn hClogWnn
      linarith only [hh]
    have hstep2 : L₀ * B * ZH * X2 ≤ Clog * W * ((Real.log 80 + 1) * logH) * (4 * (X + Y)) := by
      have hh := mul_le_mul hstep1 hX2le hX2nn (mul_nonneg hClogWnn h80logHnn)
      linarith only [hh]
    have hstep3 : Clog * W * ((Real.log 80 + 1) * logH) * (4 * (X + Y)) ≤ M * logH^2 * W * (X + Y) := by
      have hCW := mul_le_mul_of_nonneg_right hC3 hWnn
      have hh := mul_le_mul_of_nonneg_right hCW hXYnn
      linarith only [hh]
    nlinarith only [hstep2, hstep3]
  have hLHS : L₀ * (4 * Real.sqrt 5 * P + B * (32 * Real.sqrt 2 * T / (D:ℝ) + ZH * X2))
      = L₀ * (4 * Real.sqrt 5 * P) + L₀ * (B * (32 * Real.sqrt 2 * T / (D:ℝ)))
        + L₀ * (B * (ZH * X2)) := by ring
  have hRHS : M * (logA ^ 2 * P + logH ^ 2 * W * (T / (D:ℝ) + X + Y))
      = M * (logA ^ 2 * P) + M * (logH ^ 2 * W * (T / (D:ℝ))) + M * (logH ^ 2 * W * (X + Y)) := by ring
  rw [hLHS, hRHS]
  linarith only [h1, h2, h3]

end Work.FIArea4.Vflip.Vfd
