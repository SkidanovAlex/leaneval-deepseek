import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.Analysis.Asymptotics.abel_tail_bound_finite

namespace Commons.Analysis.Asymptotics

private lemma absorb_core1 {Cab m A L : ℝ} (hA : 0 < A) (hL1 : 1 ≤ L)
    (h1 : 2916 * Cab * m^6 ≤ L) :
    128 * Cab * m^6 * L ^ (-(A+23)) ≤ 1/3 := by
  have hL0 : (0:ℝ) < L := by linarith
  have hCm : Cab * m^6 ≤ L / 2916 := by linarith
  have hLneg0 : 0 ≤ L ^ (-(A+23)) := Real.rpow_nonneg hL0.le _
  have key : L * L ^ (-(A+23)) = L ^ (-(A+22)) := by
    calc L * L ^ (-(A+23)) = L^(1:ℝ) * L ^ (-(A+23)) := by rw [Real.rpow_one]
      _ = L ^ (1 + -(A+23)) := by rw [← Real.rpow_add hL0]
      _ = L ^ (-(A+22)) := by congr 1; ring
  have hle1 : L ^ (-(A+22)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  calc 128 * Cab * m^6 * L ^ (-(A+23))
      ≤ 128 * (L/2916) * L ^ (-(A+23)) := by
        apply mul_le_mul_of_nonneg_right _ hLneg0
        linarith [hCm]
    _ = (128/2916) * (L * L ^ (-(A+23))) := by ring
    _ = (128/2916) * L ^ (-(A+22)) := by rw [key]
    _ ≤ (128/2916) * 1 := by
        apply mul_le_mul_of_nonneg_left hle1 (by norm_num)
    _ ≤ 1/3 := by norm_num

private lemma absorb_core3 {Cab m A L : ℝ} (hA : 0 < A) (hL1 : 1 ≤ L)
    (h2 : 729 * Real.sqrt 2 * Cab * m^3 ≤ L) :
    32 * Real.sqrt 2 * Cab * m^3 * L ^ (-(A+23)) ≤ 1/3 := by
  have hL0 : (0:ℝ) < L := by linarith
  have hCm : Real.sqrt 2 * Cab * m^3 ≤ L / 729 := by linarith
  have hLneg0 : 0 ≤ L ^ (-(A+23)) := Real.rpow_nonneg hL0.le _
  have key : L * L ^ (-(A+23)) = L ^ (-(A+22)) := by
    calc L * L ^ (-(A+23)) = L^(1:ℝ) * L ^ (-(A+23)) := by rw [Real.rpow_one]
      _ = L ^ (1 + -(A+23)) := by rw [← Real.rpow_add hL0]
      _ = L ^ (-(A+22)) := by congr 1; ring
  have hle1 : L ^ (-(A+22)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  calc 32 * Real.sqrt 2 * Cab * m^3 * L ^ (-(A+23))
      ≤ 32 * (L/729) * L ^ (-(A+23)) := by
        apply mul_le_mul_of_nonneg_right _ hLneg0
        linarith [hCm]
    _ = (32/729) * (L * L ^ (-(A+23))) := by ring
    _ = (32/729) * L ^ (-(A+22)) := by rw [key]
    _ ≤ (32/729) * 1 := by
        apply mul_le_mul_of_nonneg_left hle1 (by norm_num)
    _ ≤ 1/3 := by norm_num

private lemma absorb_core2 {Cab m A X L : ℝ} (hCab : 0 ≤ Cab) (hm : 0 ≤ m)
    (hL1 : 1 ≤ L)
    (hlogpow : 1458 * (2:ℝ)^(5/6:ℝ) * Cab * m^5 * L^(A+18) ≤ X^(1/6:ℝ)) :
    32 * (2:ℝ)^(5/6:ℝ) * Cab * m^5 * (Real.log 4 + L/2) * L^(A+17) ≤ (1/3) * X^(1/6:ℝ) := by
  have hL0 : (0:ℝ) < L := by linarith
  have hlog4 : Real.log 4 ≤ 4 := by
    have := Real.log_le_self (show (0:ℝ) ≤ 4 by norm_num); linarith
  have hC0 : 0 ≤ (2:ℝ)^(5/6:ℝ) * Cab * m^5 * L^(A+17) := by positivity
  have hLexp : L^(A+18) = L^(A+17) * L := by
    rw [show A+18 = (A+17) + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
  have hlogpow' : 1458 * ((2:ℝ)^(5/6:ℝ) * Cab * m^5 * L^(A+17) * L) ≤ X^(1/6:ℝ) := by
    have hh := hlogpow
    rw [hLexp] at hh
    linarith [hh]
  have hle1 : 96 * (Real.log 4 + L/2) ≤ 1458 * L := by linarith [hlog4]
  have hstep : 96 * (Real.log 4 + L/2) * ((2:ℝ)^(5/6:ℝ) * Cab * m^5 * L^(A+17)) ≤ X^(1/6:ℝ) := by
    calc 96 * (Real.log 4 + L/2) * ((2:ℝ)^(5/6:ℝ) * Cab * m^5 * L^(A+17))
        ≤ (1458 * L) * ((2:ℝ)^(5/6:ℝ) * Cab * m^5 * L^(A+17)) := mul_le_mul_of_nonneg_right hle1 hC0
      _ = 1458 * ((2:ℝ)^(5/6:ℝ) * Cab * m^5 * L^(A+17) * L) := by ring
      _ ≤ X^(1/6:ℝ) := hlogpow'
  linarith [hstep]

theorem abel_tail_numeric_absorb
    (Cab m A : ℝ) (X : ℝ) (R Q : ℕ) (xa : ℕ)
    (hCab : 0 < Cab) (hm : 1 ≤ m) (hA : 0 < A)
    (hX2 : 2 ≤ X) (hPhi1 : 1 ≤ Real.log X)
    (hloglarge : max 1 (max (2916 * Cab * m^6) (729 * Real.sqrt 2 * Cab * m^3)) ≤ Real.log X)
    (hlogpow : 1458 * (2:ℝ)^(5/6:ℝ) * Cab * m^5 * (Real.log X)^(A+18) ≤ X^(1/6:ℝ))
    (hR1 : 1 ≤ R) (hRQ : R ≤ Q)
    (hRbd : (Real.log X)^(2*A+40) ≤ 2 * (R:ℝ))
    (hQbd : (Q:ℝ) ≤ Real.sqrt X / (Real.log X)^(2*A+40))
    (hxa_ub : (xa:ℝ) ≤ 2 * m^6 * X)
    (hXsq : 2 * Real.sqrt X + 2 ≤ X^2)
    (hsqrt : 4*m^6 ≤ Real.sqrt X) :
    Cab * ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ)) * (Real.log ((xa:ℝ)*(Q:ℝ)+2))^5 ≤ X * (Real.log X)^(-(A+12)) := by
  have hX0 : (0:ℝ) < X := by linarith
  have hL1 : (1:ℝ) ≤ Real.log X := hPhi1
  have hL0 : (0:ℝ) < Real.log X := by linarith
  have hm0 : (0:ℝ) < m := by linarith
  have h1 : 2916 * Cab * m^6 ≤ Real.log X :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hloglarge
  have h2 : 729 * Real.sqrt 2 * Cab * m^3 ≤ Real.log X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hloglarge
  have hxa0 : (0:ℝ) ≤ (xa:ℝ) := Nat.cast_nonneg xa
  have hQ0 : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
  have hR0 : (0:ℝ) < (R:ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hQ1 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast (le_trans hR1 hRQ)
  have hRQ' : (R:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hRQ
  have hLpow1 : (1:ℝ) ≤ (Real.log X)^(2*A+40) := Real.one_le_rpow hL1 (by linarith)
  have hLpowpos : (0:ℝ) < (Real.log X)^(2*A+40) := Real.rpow_pos_of_pos hL0 _
  -- Q ≤ sqrt X
  have hQle : (Q:ℝ) ≤ Real.sqrt X := by
    calc (Q:ℝ) ≤ Real.sqrt X / (Real.log X)^(2*A+40) := hQbd
      _ ≤ Real.sqrt X / 1 := div_le_div_of_nonneg_left (Real.sqrt_nonneg X) zero_lt_one hLpow1
      _ = Real.sqrt X := by ring
  -- log argument
  have hxaQ : (xa:ℝ)*(Q:ℝ) ≤ 2*m^6*X*(Real.sqrt X) := by
    calc (xa:ℝ)*(Q:ℝ) ≤ (2*m^6*X)*(Q:ℝ) := mul_le_mul_of_nonneg_right hxa_ub hQ0
      _ ≤ (2*m^6*X)*(Real.sqrt X) := mul_le_mul_of_nonneg_left hQle (by positivity)
  have hm6sq : 2*m^6 ≤ Real.sqrt X / 2 := by linarith
  have hxaQ2 : 2*m^6*X*(Real.sqrt X) ≤ X^2/2 := by
    have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
    have hstep1 : 2*m^6*X ≤ (Real.sqrt X/2)*X := mul_le_mul_of_nonneg_right hm6sq hX0.le
    have heq : ((Real.sqrt X/2)*X)*(Real.sqrt X) = X^2/2 := by
      have : ((Real.sqrt X/2)*X)*(Real.sqrt X) = (Real.sqrt X * Real.sqrt X) * (X/2) := by ring
      rw [this, hsq]; ring
    calc 2*m^6*X*(Real.sqrt X) = (2*m^6*X)*(Real.sqrt X) := by ring
      _ ≤ ((Real.sqrt X/2)*X)*(Real.sqrt X) := mul_le_mul_of_nonneg_right hstep1 (Real.sqrt_nonneg X)
      _ = X^2/2 := heq
  have hlogarg : (xa:ℝ)*(Q:ℝ) + 2 ≤ X^2 := by
    have h2le : (2:ℝ) ≤ X^2/2 := by nlinarith [hX2]
    linarith [hxaQ, hxaQ2, h2le]
  have hlogargpos : (0:ℝ) < (xa:ℝ)*(Q:ℝ) + 2 := by positivity
  have hlog_le : Real.log ((xa:ℝ)*(Q:ℝ)+2) ≤ 2 * Real.log X := by
    have := Real.log_le_log hlogargpos hlogarg
    rwa [Real.log_pow] at this
  have hlog_nonneg : 0 ≤ Real.log ((xa:ℝ)*(Q:ℝ)+2) :=
    Real.log_nonneg (by have : (0:ℝ) ≤ (xa:ℝ)*(Q:ℝ) := mul_nonneg hxa0 hQ0; linarith)
  have hS5 : (Real.log ((xa:ℝ)*(Q:ℝ)+2))^5 ≤ 32 * (Real.log X)^5 := by
    calc (Real.log ((xa:ℝ)*(Q:ℝ)+2))^5 ≤ (2 * Real.log X)^5 := pow_le_pow_left₀ hlog_nonneg hlog_le 5
      _ = 32 * (Real.log X)^5 := by ring
  -- term 1
  have hRinv : 1/(R:ℝ) ≤ 2 * (Real.log X)^(-(2*A+40)) := by
    have h2inv : 2 * (Real.log X)^(-(2*A+40)) = 2 / (Real.log X)^(2*A+40) := by
      rw [Real.rpow_neg hL0.le]; ring
    rw [h2inv, div_le_iff₀ hR0, div_mul_eq_mul_div, one_le_div₀ hLpowpos]
    exact hRbd
  have hT1 : (xa:ℝ)/(R:ℝ) ≤ 4*m^6*X*(Real.log X)^(-(2*A+40)) := by
    calc (xa:ℝ)/(R:ℝ) ≤ (2*m^6*X)/(R:ℝ) := div_le_div_of_nonneg_right hxa_ub hR0.le
      _ = 2*m^6*X * (1/(R:ℝ)) := by ring
      _ ≤ 2*m^6*X * (2 * (Real.log X)^(-(2*A+40))) := mul_le_mul_of_nonneg_left hRinv (by positivity)
      _ = 4*m^6*X*(Real.log X)^(-(2*A+40)) := by ring
  -- term 3
  have hxas : (xa:ℝ)^(1/2:ℝ) ≤ Real.sqrt 2 * m^3 * Real.sqrt X := by
    have h1' : (xa:ℝ)^(1/2:ℝ) ≤ (2*m^6*X)^(1/2:ℝ) := Real.rpow_le_rpow hxa0 hxa_ub (by norm_num)
    have h2' : (2*m^6*X)^(1/2:ℝ) = Real.sqrt 2 * m^3 * Real.sqrt X := by
      rw [← Real.sqrt_eq_rpow]
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*m^6)]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      have hm3 : (0:ℝ) ≤ m^3 := by positivity
      rw [show m^6 = (m^3)^2 by ring, Real.sqrt_sq hm3]
    linarith [h1', h2']
  have hT3 : (xa:ℝ)^(1/2:ℝ) * (Q:ℝ) ≤ Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40)) := by
    have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
    have hQle2 : (Q:ℝ) ≤ Real.sqrt X * (Real.log X)^(-(2*A+40)) := by
      have : Real.sqrt X * (Real.log X)^(-(2*A+40)) = Real.sqrt X / (Real.log X)^(2*A+40) := by
        rw [Real.rpow_neg hL0.le]; ring
      rw [this]; exact hQbd
    calc (xa:ℝ)^(1/2:ℝ) * (Q:ℝ) ≤ (Real.sqrt 2 * m^3 * Real.sqrt X) * (Q:ℝ) :=
          mul_le_mul_of_nonneg_right hxas hQ0
      _ ≤ (Real.sqrt 2 * m^3 * Real.sqrt X) * (Real.sqrt X * (Real.log X)^(-(2*A+40))) :=
          mul_le_mul_of_nonneg_left hQle2 (by positivity)
      _ = Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40)) := by
          have hassoc : (Real.sqrt 2 * m^3 * Real.sqrt X) * (Real.sqrt X * (Real.log X)^(-(2*A+40)))
              = (Real.sqrt 2 * m^3 * (Real.sqrt X * Real.sqrt X)) * (Real.log X)^(-(2*A+40)) := by ring
          rw [hassoc, hsq]
  -- term 2
  have hlog2nonneg : 0 ≤ Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) := by
    apply Real.log_nonneg
    have hQR0 : (0:ℝ) ≤ (Q:ℝ)/(R:ℝ) := div_nonneg hQ0 hR0.le
    linarith
  have hQR : (Q:ℝ)/(R:ℝ) ≤ (Q:ℝ) := by
    rw [div_le_iff₀ hR0]
    have : (Q:ℝ) * 1 ≤ (Q:ℝ) * (R:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hR1) hQ0
    linarith [this]
  have hlog2 : Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) ≤ Real.log 4 + Real.log X / 2 := by
    have harg_le : 2 * ((Q:ℝ)/(R:ℝ)) + 2 ≤ 4 * Real.sqrt X := by
      have ha : 2*((Q:ℝ)/(R:ℝ)) ≤ 2*(Q:ℝ) := by linarith [hQR]
      have hb : 2*(Q:ℝ) ≤ 2*Real.sqrt X := by linarith [hQle]
      have hc : (2:ℝ) ≤ 2*(Q:ℝ) := by linarith [hQ1]
      linarith
    have hpos : 0 < 2 * ((Q:ℝ)/(R:ℝ)) + 2 := by
      have hQR0 : (0:ℝ) ≤ (Q:ℝ)/(R:ℝ) := div_nonneg hQ0 hR0.le
      linarith
    have hpos2 : 0 < 4 * Real.sqrt X := by positivity
    have h := Real.log_le_log hpos harg_le
    rwa [Real.log_mul (by norm_num) (ne_of_gt (Real.sqrt_pos_of_pos hX0)),
         Real.log_sqrt hX0.le] at h
  have hxa56 : (xa:ℝ)^(5/6:ℝ) ≤ (2:ℝ)^(5/6:ℝ) * m^5 * X^(5/6:ℝ) := by
    calc (xa:ℝ)^(5/6:ℝ) ≤ (2*m^6*X)^(5/6:ℝ) := Real.rpow_le_rpow hxa0 hxa_ub (by norm_num)
      _ = (2:ℝ)^(5/6:ℝ) * m^5 * X^(5/6:ℝ) := by
          rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 2*m^6) hX0.le]
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ m^6)]
          rw [show (m^6)^(5/6:ℝ) = m^5 by
                rw [show m^6 = m^(6:ℝ) by exact (Real.rpow_natCast m 6).symm]
                rw [← Real.rpow_mul hm0.le]; norm_num]
  have hT2 : (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2)
      ≤ (2:ℝ)^(5/6:ℝ) * m^5 * X^(5/6:ℝ) * (Real.log 4 + Real.log X / 2) :=
    mul_le_mul hxa56 hlog2 hlog2nonneg (by positivity)
  -- scalars
  have hS1 := absorb_core1 (Cab:=Cab) (m:=m) (A:=A) (L:=Real.log X) hA hL1 h1
  have hS2 := absorb_core2 (Cab:=Cab) (m:=m) (A:=A) (X:=X) (L:=Real.log X) hCab.le hm0.le hL1 hlogpow
  have hS3 := absorb_core3 (Cab:=Cab) (m:=m) (A:=A) (L:=Real.log X) hA hL1 h2
  -- assembly
  have hTsum : ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ))
      ≤ 4*m^6*X*(Real.log X)^(-(2*A+40))
        + (2:ℝ)^(5/6:ℝ)*m^5*X^(5/6:ℝ)*(Real.log 4 + Real.log X/2)
        + Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40)) :=
    add_le_add (add_le_add hT1 hT2) hT3
  have hTsum_nonneg : 0 ≤ ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ)) := by
    have h1' : 0 ≤ (xa:ℝ)/(R:ℝ) := div_nonneg hxa0 hR0.le
    have h2' : 0 ≤ (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) :=
      mul_nonneg (Real.rpow_nonneg hxa0 _) hlog2nonneg
    have h3' : 0 ≤ (xa:ℝ)^(1/2:ℝ) * (Q:ℝ) := mul_nonneg (Real.rpow_nonneg hxa0 _) hQ0
    linarith
  have hstep1 : Cab * ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ)) * (Real.log ((xa:ℝ)*(Q:ℝ)+2))^5
      ≤ Cab * ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ)) * (32 * (Real.log X)^5) :=
    mul_le_mul_of_nonneg_left hS5 (mul_nonneg hCab.le hTsum_nonneg)
  have hstep2 : Cab * ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ)) * (32 * (Real.log X)^5)
      ≤ Cab * (4*m^6*X*(Real.log X)^(-(2*A+40))
          + (2:ℝ)^(5/6:ℝ)*m^5*X^(5/6:ℝ)*(Real.log 4 + Real.log X/2)
          + Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5) := by
    have hG : 0 ≤ Cab * (32 * (Real.log X)^5) := by positivity
    calc Cab * ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ)) * (32 * (Real.log X)^5)
        = (Cab * (32 * (Real.log X)^5)) * ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ)) := by ring
      _ ≤ (Cab * (32 * (Real.log X)^5)) * (4*m^6*X*(Real.log X)^(-(2*A+40))
          + (2:ℝ)^(5/6:ℝ)*m^5*X^(5/6:ℝ)*(Real.log 4 + Real.log X/2)
          + Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40))) := mul_le_mul_of_nonneg_left hTsum hG
      _ = Cab * (4*m^6*X*(Real.log X)^(-(2*A+40))
          + (2:ℝ)^(5/6:ℝ)*m^5*X^(5/6:ℝ)*(Real.log 4 + Real.log X/2)
          + Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5) := by ring
  -- identities
  have hA1 : Cab * (4*m^6*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5)
      = (X * (Real.log X)^(-(A+12))) * (128 * Cab * m^6 * (Real.log X)^(-(A+23))) := by
    have hL5 : (Real.log X)^5 = (Real.log X)^(5:ℝ) := (Real.rpow_natCast _ 5).symm
    have hcmb : (Real.log X)^(-(2*A+40)) * (Real.log X)^(5:ℝ) = (Real.log X)^(-(2*A+35)) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    have hcmb2 : (Real.log X)^(-(2*A+35)) = (Real.log X)^(-(A+12)) * (Real.log X)^(-(A+23)) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    have hrw : Cab * (4*m^6*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^(5:ℝ))
        = (128 * Cab * m^6 * X) * ((Real.log X)^(-(2*A+40)) * (Real.log X)^(5:ℝ)) := by ring
    rw [hL5, hrw, hcmb, hcmb2]; ring
  have hA3 : Cab * (Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5)
      = (X * (Real.log X)^(-(A+12))) * (32 * Real.sqrt 2 * Cab * m^3 * (Real.log X)^(-(A+23))) := by
    have hL5 : (Real.log X)^5 = (Real.log X)^(5:ℝ) := (Real.rpow_natCast _ 5).symm
    have hcmb : (Real.log X)^(-(2*A+40)) * (Real.log X)^(5:ℝ) = (Real.log X)^(-(2*A+35)) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    have hcmb2 : (Real.log X)^(-(2*A+35)) = (Real.log X)^(-(A+12)) * (Real.log X)^(-(A+23)) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    have hrw : Cab * (Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^(5:ℝ))
        = (32 * Real.sqrt 2 * Cab * m^3 * X) * ((Real.log X)^(-(2*A+40)) * (Real.log X)^(5:ℝ)) := by ring
    rw [hL5, hrw, hcmb, hcmb2]; ring
  have hA2 : Cab * ((2:ℝ)^(5/6:ℝ) * m^5 * X^(5/6:ℝ) * (Real.log 4 + Real.log X / 2)) * (32 * (Real.log X)^5)
      = (32 * (2:ℝ)^(5/6:ℝ) * Cab * m^5 * (Real.log 4 + Real.log X / 2) * (Real.log X)^(A+17))
        * (X^(5/6:ℝ) * (Real.log X)^(-(A+12))) := by
    have hL5 : (Real.log X)^5 = (Real.log X)^(5:ℝ) := (Real.rpow_natCast _ 5).symm
    have hcmb : (Real.log X)^(5:ℝ) = (Real.log X)^(A+17) * (Real.log X)^(-(A+12)) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    rw [hL5, hcmb]; ring
  -- term bounds
  have hterm1 : Cab * (4*m^6*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5)
      ≤ (1/3) * (X * (Real.log X)^(-(A+12))) := by
    rw [hA1]
    have hX0' : 0 ≤ X * (Real.log X)^(-(A+12)) :=
      mul_nonneg hX0.le (Real.rpow_nonneg hL0.le _)
    calc (X * (Real.log X)^(-(A+12))) * (128 * Cab * m^6 * (Real.log X)^(-(A+23)))
        ≤ (X * (Real.log X)^(-(A+12))) * (1/3) := mul_le_mul_of_nonneg_left hS1 hX0'
      _ = (1/3) * (X * (Real.log X)^(-(A+12))) := by ring
  have hterm3 : Cab * (Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5)
      ≤ (1/3) * (X * (Real.log X)^(-(A+12))) := by
    rw [hA3]
    have hX0' : 0 ≤ X * (Real.log X)^(-(A+12)) :=
      mul_nonneg hX0.le (Real.rpow_nonneg hL0.le _)
    calc (X * (Real.log X)^(-(A+12))) * (32 * Real.sqrt 2 * Cab * m^3 * (Real.log X)^(-(A+23)))
        ≤ (X * (Real.log X)^(-(A+12))) * (1/3) := mul_le_mul_of_nonneg_left hS3 hX0'
      _ = (1/3) * (X * (Real.log X)^(-(A+12))) := by ring
  have hterm2 : Cab * ((2:ℝ)^(5/6:ℝ) * m^5 * X^(5/6:ℝ) * (Real.log 4 + Real.log X / 2)) * (32 * (Real.log X)^5)
      ≤ (1/3) * (X * (Real.log X)^(-(A+12))) := by
    rw [hA2]
    have hXle : 0 ≤ X^(5/6:ℝ) * (Real.log X)^(-(A+12)) :=
      mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hL0.le _)
    have hh := mul_le_mul_of_nonneg_right hS2 hXle
    have hXpow : X^(1/6:ℝ) * X^(5/6:ℝ) = X := by rw [← Real.rpow_add hX0]; norm_num
    calc (32 * (2:ℝ)^(5/6:ℝ) * Cab * m^5 * (Real.log 4 + Real.log X / 2) * (Real.log X)^(A+17))
            * (X^(5/6:ℝ) * (Real.log X)^(-(A+12)))
        ≤ ((1/3) * X^(1/6:ℝ)) * (X^(5/6:ℝ) * (Real.log X)^(-(A+12))) := hh
      _ = (1/3) * (X * (Real.log X)^(-(A+12))) := by
          have hassoc : ((1/3) * X^(1/6:ℝ)) * (X^(5/6:ℝ) * (Real.log X)^(-(A+12)))
              = (1/3) * (X^(1/6:ℝ) * X^(5/6:ℝ)) * (Real.log X)^(-(A+12)) := by ring
          rw [hassoc, hXpow]; ring
  have hBsum : Cab * (4*m^6*X*(Real.log X)^(-(2*A+40))
        + (2:ℝ)^(5/6:ℝ)*m^5*X^(5/6:ℝ)*(Real.log 4 + Real.log X/2)
        + Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5)
      ≤ X * (Real.log X)^(-(A+12)) := by
    have hexp : Cab * (4*m^6*X*(Real.log X)^(-(2*A+40))
          + (2:ℝ)^(5/6:ℝ)*m^5*X^(5/6:ℝ)*(Real.log 4 + Real.log X/2)
          + Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5)
        = Cab * (4*m^6*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5)
          + Cab * ((2:ℝ)^(5/6:ℝ)*m^5*X^(5/6:ℝ)*(Real.log 4 + Real.log X/2)) * (32 * (Real.log X)^5)
          + Cab * (Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5) := by ring
    rw [hexp]
    linarith [hterm1, hterm2, hterm3]
  calc Cab * ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ)) * (Real.log ((xa:ℝ)*(Q:ℝ)+2))^5
      ≤ Cab * ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ) * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ)) * (32 * (Real.log X)^5) := hstep1
    _ ≤ Cab * (4*m^6*X*(Real.log X)^(-(2*A+40))
          + (2:ℝ)^(5/6:ℝ)*m^5*X^(5/6:ℝ)*(Real.log 4 + Real.log X/2)
          + Real.sqrt 2*m^3*X*(Real.log X)^(-(2*A+40))) * (32 * (Real.log X)^5) := hstep2
    _ ≤ X * (Real.log X)^(-(A+12)) := hBsum

end Commons.Analysis.Asymptotics