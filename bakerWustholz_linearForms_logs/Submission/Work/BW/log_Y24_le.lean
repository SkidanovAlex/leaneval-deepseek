import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_blaschke_eta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Auxiliary logarithm bound: if `0 < a ≤ t` and `log a ≤ L` then
`log t ≤ L + t/a - 1`.  Obtained from `log y ≤ y - 1` applied to `y = t/a`. -/
lemma bw_log_le_of_log_le {a t L : ℝ} (ha : 0 < a) (hat : a ≤ t) (hL : Real.log a ≤ L) :
    Real.log t ≤ L + t / a - 1 := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hta : 0 < t / a := div_pos ht ha
  have h1 : Real.log (t / a) = Real.log t - Real.log a :=
    Real.log_div (ne_of_gt ht) (ne_of_gt ha)
  have h2 : Real.log (t / a) ≤ t / a - 1 := Real.log_le_sub_one_of_pos hta
  linarith

theorem log_Y24_le {Sp X : ℝ} (hSp : 608 ≤ Sp) (hX1 : 1 ≤ X) (hX2 : X ≤ 2.003) (Tp : ℕ) :
    ((Tp : ℝ) + 1) * Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1 / 3 : ℝ))⁻¹ ^ 2 * Sp ^ 2 *
        Real.exp (2 * Sp) * X ^ (2 * Sp + 1)) +
      Real.log ((2 * Sp + 1) * ((Tp : ℝ) + 1)) ≤
    3.43 * Sp * ((Tp : ℝ) + 1) + (((Tp : ℝ) + 1) * (0.05 * Sp + 1) + Real.log ((Tp : ℝ) + 1)) := by
  set n : ℝ := (Tp : ℝ) + 1 with hn
  have hTp : (0:ℝ) ≤ (Tp:ℝ) := Nat.cast_nonneg Tp
  have hn1 : (1:ℝ) ≤ n := by rw [hn]; linarith
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hSp0 : 0 < Sp := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  -- bound on `log X`
  have hlogX : Real.log X ≤ 7/10 := by
    have h2 : 0 < X / 2 := by linarith
    have h1 : Real.log X = Real.log 2 + Real.log (X/2) := by
      rw [← Real.log_mul (show (2:ℝ) ≠ 0 by norm_num) (ne_of_gt h2)]
      congr 1; ring
    have h3 : Real.log (X/2) ≤ X/2 - 1 := Real.log_le_sub_one_of_pos h2
    have h4 : X / 2 - 1 ≤ 2.003/2 - 1 := by linarith
    linarith [Real.log_two_lt_d9]
  -- bound on the constant factor `(2π/3)⁻¹ * (1-1/3)⁻¹ ^ 2 = 27/(8π)`
  have hlogC : Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1/3:ℝ))⁻¹ ^ 2) ≤ 1 := by
    have hCpos : 0 < (2 * Real.pi / 3)⁻¹ * (1 - (1/3:ℝ))⁻¹ ^ 2 := by positivity
    have hle : (2 * Real.pi / 3)⁻¹ * (1 - (1/3:ℝ))⁻¹ ^ 2 ≤ 2 := by
      have h1 : (1 - (1/3:ℝ))⁻¹ ^ 2 = 9/4 := by norm_num
      have h2 : (2 * Real.pi / 3)⁻¹ ≤ (1/2 : ℝ) := by
        have : (2:ℝ)⁻¹ = 1/2 := by norm_num
        rw [← this, inv_le_inv₀ (by positivity) (by norm_num)]
        linarith [Real.pi_gt_three]
      calc (2 * Real.pi / 3)⁻¹ * (1 - (1/3:ℝ))⁻¹ ^ 2 = (2 * Real.pi / 3)⁻¹ * (9/4) := by rw [h1]
        _ ≤ (1/2) * (9/4) := by apply mul_le_mul_of_nonneg_right h2; norm_num
        _ ≤ 2 := by norm_num
    have h4 := Real.log_le_sub_one_of_pos hCpos
    linarith
  -- linear upper bound for `log Sp`
  have hlogSp : Real.log Sp ≤ 9 + Sp/608 := by
    have h608 : Real.log (608:ℝ) ≤ 10 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h2 : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
      have h3 : (2:ℝ)^10 ≤ (Real.exp 1)^10 := pow_le_pow_left₀ (by norm_num) h2 10
      have h4 : Real.exp 10 = (Real.exp 1)^10 := by rw [← Real.exp_nat_mul (1:ℝ) 10]; norm_num
      rw [h4]; norm_num at h3 ⊢; linarith
    have := bw_log_le_of_log_le (a := 608) (by norm_num) hSp h608
    linarith
  -- linear upper bound for `log (2Sp+1)`
  have hlog2 : Real.log (2*Sp+1) ≤ 11 + (2*Sp+1)/1217 := by
    have h1217 : Real.log (1217:ℝ) ≤ 12 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h2 : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
      have h3 : (2:ℝ)^12 ≤ (Real.exp 1)^12 := pow_le_pow_left₀ (by norm_num) h2 12
      have h4 : Real.exp 12 = (Real.exp 1)^12 := by rw [← Real.exp_nat_mul (1:ℝ) 12]; norm_num
      rw [h4]; norm_num at h3 ⊢; linarith
    have h : (1217:ℝ) ≤ 2*Sp+1 := by linarith
    have := bw_log_le_of_log_le (a := 1217) (by norm_num) h h1217
    linarith
  -- expansion of the logarithm of the big product
  have hAeq : Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1/3:ℝ))⁻¹ ^ 2 * Sp^2 * Real.exp (2*Sp) * X^(2*Sp+1))
      = Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1/3:ℝ))⁻¹ ^ 2) + 2*Real.log Sp + 2*Sp + (2*Sp+1)*Real.log X := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow Sp 2, Real.log_exp, Real.log_rpow hX0]
    push_cast; ring
  -- upper bound on `log A`
  have hlogA : Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1/3:ℝ))⁻¹ ^ 2 * Sp^2 * Real.exp (2*Sp) * X^(2*Sp+1))
      ≤ 1 + 2*Real.log Sp + 2*Sp + (2*Sp+1)*(7/10) := by
    rw [hAeq]
    have hmm := mul_le_mul_of_nonneg_left hlogX (by linarith : (0:ℝ) ≤ 2*Sp+1)
    linarith
  have hFbound : 2*Real.log Sp + 2*Sp + (2*Sp+1)*(7/10) + 1 - (3.48*Sp + 1) ≤ 18.7 - (583/7600)*Sp := by
    linarith [hlogSp]
  have hFneg : 2*Real.log Sp + 2*Sp + (2*Sp+1)*(7/10) + 1 - (3.48*Sp + 1) ≤ 0 := by
    have hsp : (18.7 : ℝ) - (583/7600)*Sp ≤ 0 := by
      have hcoef : (0:ℝ) < (583/7600 : ℝ) := by norm_num
      have hm := mul_le_mul_of_nonneg_left hSp (le_of_lt hcoef)
      have hval : (18.7 : ℝ) ≤ (583/7600 : ℝ) * 608 := by norm_num
      linarith
    linarith [hFbound]
  have hFE : 2*Real.log Sp + 2*Sp + (2*Sp+1)*(7/10) + 1 - (3.48*Sp + 1) + Real.log (2*Sp+1) ≤ 0 := by
    have hsp : (29.7 : ℝ) + 1/1217 ≤ (583/7600 - 2/1217)*Sp := by
      have hcoef : (0:ℝ) < 583/7600 - 2/1217 := by norm_num
      have hm := mul_le_mul_of_nonneg_left hSp (le_of_lt hcoef)
      have hval : (29.7 : ℝ) + 1/1217 ≤ (583/7600 - 2/1217)*608 := by norm_num
      linarith
    linarith [hFbound, hlog2, hsp]
  -- the main estimate, with `log n` cancelled on both sides
  have hcore : n*(Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1/3:ℝ))⁻¹ ^ 2 * Sp^2 * Real.exp (2*Sp) * X^(2*Sp+1))) + Real.log (2*Sp+1)
      ≤ 3.43*Sp*n + n*(0.05*Sp+1) := by
    have h1 : n * Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1/3:ℝ))⁻¹ ^ 2 * Sp^2 * Real.exp (2*Sp) * X^(2*Sp+1))
        ≤ n * (1 + 2*Real.log Sp + 2*Sp + (2*Sp+1)*(7/10)) :=
      mul_le_mul_of_nonneg_left hlogA (le_of_lt hn0)
    have hFG : n * (1 + 2*Real.log Sp + 2*Sp + (2*Sp+1)*(7/10))
        ≤ n*(3.48*Sp+1) + (2*Real.log Sp + 2*Sp + (2*Sp+1)*(7/10) + 1 - (3.48*Sp+1)) := by
      have hm : n * (2*Real.log Sp + 2*Sp + (2*Sp+1)*(7/10) + 1 - (3.48*Sp+1))
          ≤ (2*Real.log Sp + 2*Sp + (2*Sp+1)*(7/10) + 1 - (3.48*Sp+1)) := by
        have h : (n-1)*(2*Real.log Sp + 2*Sp + (2*Sp+1)*(7/10) + 1 - (3.48*Sp+1)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) hFneg
        nlinarith [h]
      nlinarith [hm]
    have hG : n*(3.48*Sp+1) = 3.43*Sp*n + n*(0.05*Sp+1) := by ring
    linarith [h1, hFG, hFE, hG]
  have hlogmul : Real.log ((2*Sp+1)*n) = Real.log (2*Sp+1) + Real.log n :=
    Real.log_mul (by linarith) (ne_of_gt hn0)
  rw [hlogmul]
  linarith [hcore]

end Work.BW
