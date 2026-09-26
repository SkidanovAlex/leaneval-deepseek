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

private lemma sigma_eq_sigmaFast (n : ℕ) : (ArithmeticFunction.sigma 1 n : ℕ) = sigmaFast n := by
  rw [ArithmeticFunction.sigma_apply]
  unfold Nat.divisors
  rw [Finset.sum_filter]
  simp only [pow_one]
  rw [← sigmaFastAux_eq_sum n n]
  unfold sigmaFast
  rfl

private theorem sigma_le_13440_range_3701_3800_chk_3701 :
    (List.range' 3701 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 13440) = true := by
  decide +kernel

private theorem sigma_le_13440_range_3701_3800_chk_3711 :
    (List.range' 3711 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 13440) = true := by
  decide +kernel

private theorem sigma_le_13440_range_3701_3800_chk_3721 :
    (List.range' 3721 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 13440) = true := by
  decide +kernel

private theorem sigma_le_13440_range_3701_3800_chk_3731 :
    (List.range' 3731 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 13440) = true := by
  decide +kernel

private theorem sigma_le_13440_range_3701_3800_chk_3741 :
    (List.range' 3741 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 13440) = true := by
  decide +kernel

private theorem sigma_le_13440_range_3701_3800_chk_3751 :
    (List.range' 3751 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 13440) = true := by
  decide +kernel

private theorem sigma_le_13440_range_3701_3800_chk_3761 :
    (List.range' 3761 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 13440) = true := by
  decide +kernel

private theorem sigma_le_13440_range_3701_3800_chk_3771 :
    (List.range' 3771 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 13440) = true := by
  decide +kernel

private theorem sigma_le_13440_range_3701_3800_chk_3781 :
    (List.range' 3781 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 13440) = true := by
  decide +kernel

private theorem sigma_le_13440_range_3701_3800_chk_3791 :
    (List.range' 3791 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 13440) = true := by
  decide +kernel

theorem sigma_le_13440_range_3701_3800 (n : ℕ) (hL : 3701 ≤ n) (hU : n ≤ 3800) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 13440 := by
  if h : n < 3711 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_13440_range_3701_3800_chk_3701 n (by omega) h
  else
    if h : n < 3721 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_13440_range_3701_3800_chk_3711 n (by omega) h
    else
      if h : n < 3731 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_13440_range_3701_3800_chk_3721 n (by omega) h
      else
        if h : n < 3741 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_13440_range_3701_3800_chk_3731 n (by omega) h
        else
          if h : n < 3751 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_13440_range_3701_3800_chk_3741 n (by omega) h
          else
            if h : n < 3761 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_13440_range_3701_3800_chk_3751 n (by omega) h
            else
              if h : n < 3771 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_13440_range_3701_3800_chk_3761 n (by omega) h
              else
                if h : n < 3781 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_13440_range_3701_3800_chk_3771 n (by omega) h
                else
                  if h : n < 3791 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_13440_range_3701_3800_chk_3781 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_13440_range_3701_3800_chk_3791 n (by omega) (by omega)

end Commons.NumberTheory.Lagarias