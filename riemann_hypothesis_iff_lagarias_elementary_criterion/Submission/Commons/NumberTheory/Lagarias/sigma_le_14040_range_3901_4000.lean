import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Submission.Commons.NumberTheory.SigmaCheck

open scoped ArithmeticFunction.sigma

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

private lemma sigma_eq_sigmaFast (n : ℕ) :
    (ArithmeticFunction.sigma 1 n : ℕ) = sigmaFast n := by
  rw [ArithmeticFunction.sigma_apply]
  unfold Nat.divisors
  rw [Finset.sum_filter]
  simp only [pow_one]
  rw [← sigmaFastAux_eq_sum n n]
  unfold sigmaFast
  rfl

private theorem sigma_le_14040_range_3901_4000_chk_3901 :
    (List.range' 3901 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 14040) = true := by
  decide +kernel

private theorem sigma_le_14040_range_3901_4000_chk_3911 :
    (List.range' 3911 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 14040) = true := by
  decide +kernel

private theorem sigma_le_14040_range_3901_4000_chk_3921 :
    (List.range' 3921 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 14040) = true := by
  decide +kernel

private theorem sigma_le_14040_range_3901_4000_chk_3931 :
    (List.range' 3931 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 14040) = true := by
  decide +kernel

private theorem sigma_le_14040_range_3901_4000_chk_3941 :
    (List.range' 3941 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 14040) = true := by
  decide +kernel

private theorem sigma_le_14040_range_3901_4000_chk_3951 :
    (List.range' 3951 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 14040) = true := by
  decide +kernel

private theorem sigma_le_14040_range_3901_4000_chk_3961 :
    (List.range' 3961 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 14040) = true := by
  decide +kernel

private theorem sigma_le_14040_range_3901_4000_chk_3971 :
    (List.range' 3971 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 14040) = true := by
  decide +kernel

private theorem sigma_le_14040_range_3901_4000_chk_3981 :
    (List.range' 3981 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 14040) = true := by
  decide +kernel

private theorem sigma_le_14040_range_3901_4000_chk_3991 :
    (List.range' 3991 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 14040) = true := by
  decide +kernel

theorem sigma_le_14040_range_3901_4000 (n : ℕ) (hL : 3901 ≤ n) (hU : n ≤ 4000) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 14040 := by
  if h : n < 3911 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_14040_range_3901_4000_chk_3901 n (by omega) h
  else
    if h : n < 3921 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_14040_range_3901_4000_chk_3911 n (by omega) h
    else
      if h : n < 3931 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_14040_range_3901_4000_chk_3921 n (by omega) h
      else
        if h : n < 3941 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_14040_range_3901_4000_chk_3931 n (by omega) h
        else
          if h : n < 3951 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_14040_range_3901_4000_chk_3941 n (by omega) h
          else
            if h : n < 3961 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_14040_range_3901_4000_chk_3951 n (by omega) h
            else
              if h : n < 3971 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_14040_range_3901_4000_chk_3961 n (by omega) h
              else
                if h : n < 3981 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_14040_range_3901_4000_chk_3971 n (by omega) h
                else
                  if h : n < 3991 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_14040_range_3901_4000_chk_3981 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_14040_range_3901_4000_chk_3991 n (by omega) (by omega)

end Commons.NumberTheory.Lagarias