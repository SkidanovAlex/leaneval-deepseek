import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Submission.Commons.NumberTheory.SigmaCheck

namespace Commons.NumberTheory.Lagarias

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def sigmaFastAux : ℕ → ℕ → ℕ
  | _n, 0 => 0
  | n, k + 1 => sigmaFastAux n k + if n % (k + 1) = 0 then (k + 1) else 0

private def sigmaFast (n : ℕ) : ℕ := sigmaFastAux n n

private lemma sigmaFastAux_eq_sum (n k : ℕ) :
    sigmaFastAux n k = ∑ i ∈ Finset.Ico 1 (k + 1), if i ∣ n then i else 0 := by
  induction k with
  | zero =>
      simp [sigmaFastAux]
  | succ k ih =>
      rw [sigmaFastAux]
      rw [ih]
      rw [Finset.sum_Ico_succ_top (show 1 ≤ k + 1 by omega)]
      simp [Nat.dvd_iff_mod_eq_zero, add_comm]

private lemma sigma_eq_sigmaFast (n : ℕ) : (ArithmeticFunction.sigma 1 n : ℕ) = sigmaFast n := by
  rw [ArithmeticFunction.sigma_apply]
  unfold Nat.divisors
  rw [Finset.sum_filter]
  simp only [pow_one]
  rw [← sigmaFastAux_eq_sum n n]
  unfold sigmaFast
  rfl

private theorem sigma_le_12493_range_3501_3600_chk_3501 :
    (List.range' 3501 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12493) = true := by
  decide +kernel

private theorem sigma_le_12493_range_3501_3600_chk_3511 :
    (List.range' 3511 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12493) = true := by
  decide +kernel

private theorem sigma_le_12493_range_3501_3600_chk_3521 :
    (List.range' 3521 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12493) = true := by
  decide +kernel

private theorem sigma_le_12493_range_3501_3600_chk_3531 :
    (List.range' 3531 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12493) = true := by
  decide +kernel

private theorem sigma_le_12493_range_3501_3600_chk_3541 :
    (List.range' 3541 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12493) = true := by
  decide +kernel

private theorem sigma_le_12493_range_3501_3600_chk_3551 :
    (List.range' 3551 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12493) = true := by
  decide +kernel

private theorem sigma_le_12493_range_3501_3600_chk_3561 :
    (List.range' 3561 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12493) = true := by
  decide +kernel

private theorem sigma_le_12493_range_3501_3600_chk_3571 :
    (List.range' 3571 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12493) = true := by
  decide +kernel

private theorem sigma_le_12493_range_3501_3600_chk_3581 :
    (List.range' 3581 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12493) = true := by
  decide +kernel

private theorem sigma_le_12493_range_3501_3600_chk_3591 :
    (List.range' 3591 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12493) = true := by
  decide +kernel

theorem sigma_le_12493_range_3501_3600 (n : ℕ) (hL : 3501 ≤ n) (hU : n ≤ 3600) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 12493 := by
  if h : n < 3511 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12493_range_3501_3600_chk_3501 n (by omega) h
  else
    if h : n < 3521 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12493_range_3501_3600_chk_3511 n (by omega) h
    else
      if h : n < 3531 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12493_range_3501_3600_chk_3521 n (by omega) h
      else
        if h : n < 3541 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12493_range_3501_3600_chk_3531 n (by omega) h
        else
          if h : n < 3551 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12493_range_3501_3600_chk_3541 n (by omega) h
          else
            if h : n < 3561 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12493_range_3501_3600_chk_3551 n (by omega) h
            else
              if h : n < 3571 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12493_range_3501_3600_chk_3561 n (by omega) h
              else
                if h : n < 3581 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12493_range_3501_3600_chk_3571 n (by omega) h
                else
                  if h : n < 3591 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12493_range_3501_3600_chk_3581 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12493_range_3501_3600_chk_3591 n (by omega) (by omega)

end Commons.NumberTheory.Lagarias