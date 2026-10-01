import Mathlib

namespace Work.ZeroDensity.Ingham

theorem critTailPointwiseCore (A T : ℝ) (hA : 100 ≤ A) (hT : 2 ≤ T)
    (hsq : Real.sqrt T ≤ Real.exp ((A * Real.log (A * T)) / 100))
    (hT4 : T ^ 4 ≤ Real.exp ((A * Real.log (A * T)) / 25))
    (hpow : (1 + A * Real.log (A * T)) ^ 10 ≤ Real.exp ((A * Real.log (A * T)) / 4)) :
    Real.sqrt T * (3 + T + A * Real.log (A * T)) ^ 4
        * (1 + A * Real.log (A * T)) ^ 6
        * Real.exp (-(Real.pi / 2) * (A * Real.log (A * T)))
      ≤ (5 / 2 : ℝ) ^ 4
        * Real.exp (-(Real.pi / 2 - 3 / 10) * (A * Real.log (A * T))) := by
  set L := A * Real.log (A * T) with hL
  have hApos : (0:ℝ) < A := by linarith
  have hTpos : (0:ℝ) < T := by linarith
  have hATpos : (0:ℝ) < A * T := mul_pos hApos hTpos
  have hAT200 : (200:ℝ) ≤ A * T := by
    have := mul_le_mul hA hT (show (0:ℝ) ≤ 2 by norm_num) (show (0:ℝ) ≤ A by linarith)
    linarith
  have hlog2 : (2:ℝ) ≤ Real.log (A * T) := by
    rw [Real.le_log_iff_exp_le hATpos]
    have he2 : Real.exp 2 ≤ 9 := by
      have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h1]
      have hlt : Real.exp 1 < 3 := Real.exp_one_lt_three
      have hp : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
      nlinarith [hp, hlt]
    linarith
  have hL200 : (200:ℝ) ≤ L := by
    rw [hL]
    have := mul_le_mul hA hlog2 (show (0:ℝ) ≤ 2 by norm_num) (show (0:ℝ) ≤ A by linarith)
    linarith
  have hexp100 : (3:ℝ) ≤ Real.exp (L/100) := by
    have := Real.add_one_le_exp (L/100); linarith
  have hexp40 : (3:ℝ) ≤ Real.exp (L/40) := by
    have := Real.add_one_le_exp (L/40); linarith
  have hexp25 : (1296/625 : ℝ) ≤ Real.exp (L/25) := by
    have := Real.add_one_le_exp (L/25); linarith
  have hTle : T ≤ Real.exp (L/100) := by
    have heq : Real.exp (L/25) = (Real.exp (L/100))^4 := by
      have h : Real.exp ((4:ℝ) * (L/100)) = (Real.exp (L/100))^4 := Real.exp_nat_mul (L/100) 4
      rw [show L/25 = (4:ℝ) * (L/100) by ring]
      exact h
    have h4 : T^4 ≤ (Real.exp (L/100))^4 := by rw [← heq]; exact hT4
    exact (pow_le_pow_iff_left₀ (show (0:ℝ) ≤ T by linarith) (le_of_lt (Real.exp_pos _))
      (by norm_num : (4:ℕ) ≠ 0)).mp h4
  have h1Lle : 1 + L ≤ Real.exp (L/40) := by
    have heq : Real.exp (L/4) = (Real.exp (L/40))^10 := by
      have h : Real.exp ((10:ℝ) * (L/40)) = (Real.exp (L/40))^10 := Real.exp_nat_mul (L/40) 10
      rw [show L/4 = (10:ℝ) * (L/40) by ring]
      exact h
    have h10 : (1+L)^10 ≤ (Real.exp (L/40))^10 := by rw [← heq]; exact hpow
    exact (pow_le_pow_iff_left₀ (show (0:ℝ) ≤ 1+L by linarith) (le_of_lt (Real.exp_pos _))
      (by norm_num : (10:ℕ) ≠ 0)).mp h10
  have hLle40 : L ≤ Real.exp (L/40) := by linarith
  have hTle40 : T ≤ Real.exp (L/40) := by
    have : Real.exp (L/100) ≤ Real.exp (L/40) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hsum : 3 + T + L ≤ 3 * Real.exp (L/40) := by linarith
  have hsum4 : (3+T+L)^4 ≤ (3 * Real.exp (L/40))^4 :=
    pow_le_pow_left₀ (show (0:ℝ) ≤ 3+T+L by linarith) hsum 4
  have h1L6 : (1+L)^6 ≤ (Real.exp (L/40))^6 :=
    pow_le_pow_left₀ (show (0:ℝ) ≤ 1+L by linarith) h1Lle 6
  have hb : Real.sqrt T * (3+T+L)^4 * (1+L)^6
      ≤ Real.exp (L/100) * (3*Real.exp (L/40))^4 * (Real.exp (L/40))^6 := by
    have hb0 : Real.sqrt T * (3+T+L)^4 ≤ Real.exp (L/100) * (3*Real.exp (L/40))^4 :=
      mul_le_mul hsq hsum4 (by positivity) (le_of_lt (Real.exp_pos _))
    exact mul_le_mul hb0 h1L6 (by positivity) (by positivity)
  have hmain : Real.exp (L/100) * (3*Real.exp (L/40))^4 * (Real.exp (L/40))^6
      = 81 * Real.exp (13/50 * L) := by
    have he4e6 : (Real.exp (L/40))^4 * (Real.exp (L/40))^6 = Real.exp (L/4) := by
      have h : Real.exp ((10:ℝ) * (L/40)) = (Real.exp (L/40))^10 := Real.exp_nat_mul (L/40) 10
      rw [← pow_add, ← h]
      congr 1
      ring
    have hee : Real.exp (L/100) * Real.exp (L/4) = Real.exp (13/50 * L) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [mul_pow, show (3:ℝ)^4 = 81 by norm_num,
      show Real.exp (L/100) * (81 * (Real.exp (L/40))^4) * (Real.exp (L/40))^6
        = 81 * (Real.exp (L/100) * ((Real.exp (L/40))^4 * (Real.exp (L/40))^6)) by ring,
      he4e6, hee]
  have hnum : (81:ℝ) * Real.exp (13/50 * L) ≤ (5/2)^4 * Real.exp (3/10 * L) := by
    have hsplit : Real.exp (3/10 * L) = Real.exp (L/25) * Real.exp (13/50 * L) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit, show (5/2:ℝ)^4 = 625/16 by norm_num]
    have hcoef : (81:ℝ) ≤ 625/16 * Real.exp (L/25) := by linarith [hexp25]
    have hE : (0:ℝ) ≤ Real.exp (13/50 * L) := le_of_lt (Real.exp_pos _)
    calc (81:ℝ) * Real.exp (13/50 * L)
        ≤ (625/16 * Real.exp (L/25)) * Real.exp (13/50 * L) :=
          mul_le_mul_of_nonneg_right hcoef hE
      _ = 625/16 * (Real.exp (L/25) * Real.exp (13/50 * L)) := by ring
  have hfinal : Real.sqrt T * (3+T+L)^4 * (1+L)^6 ≤ (5/2)^4 * Real.exp (3/10 * L) :=
    le_trans hb (le_trans (le_of_eq hmain) hnum)
  calc Real.sqrt T * (3+T+L)^4 * (1+L)^6 * Real.exp (-(Real.pi/2) * L)
      ≤ ((5/2)^4 * Real.exp (3/10 * L)) * Real.exp (-(Real.pi/2) * L) :=
        mul_le_mul_of_nonneg_right hfinal (le_of_lt (Real.exp_pos _))
    _ = (5/2)^4 * Real.exp (-(Real.pi/2 - 3/10) * L) := by
        have hexp : Real.exp (3/10 * L) * Real.exp (-(Real.pi/2) * L)
            = Real.exp (-(Real.pi/2 - 3/10) * L) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [show (5/2:ℝ)^4 * Real.exp (3/10*L) * Real.exp (-(Real.pi/2)*L)
            = (5/2)^4 * (Real.exp (3/10*L) * Real.exp (-(Real.pi/2)*L)) by ring, hexp]

end Work.ZeroDensity.Ingham
