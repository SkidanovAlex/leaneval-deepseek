import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Submission.Commons.NumberTheory.SigmaCheck

namespace Commons.NumberTheory.Lagarias

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

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

private theorem sigma_le_4914_range_1440_1500_chk_1440 :
    (List.range' 1440 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4914) = true := by
  decide +kernel

private theorem sigma_le_4914_range_1440_1500_chk_1450 :
    (List.range' 1450 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4914) = true := by
  decide +kernel

private theorem sigma_le_4914_range_1440_1500_chk_1460 :
    (List.range' 1460 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4914) = true := by
  decide +kernel

private theorem sigma_le_4914_range_1440_1500_chk_1470 :
    (List.range' 1470 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4914) = true := by
  decide +kernel

private theorem sigma_le_4914_range_1440_1500_chk_1480 :
    (List.range' 1480 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4914) = true := by
  decide +kernel

private theorem sigma_le_4914_range_1440_1500_chk_1490 :
    (List.range' 1490 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4914) = true := by
  decide +kernel

private theorem sigma_le_4914_range_1440_1500_chk_1500 :
    (List.range' 1500 1).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4914) = true := by
  decide +kernel

theorem sigma_le_4914_range_1440_1500 (n : ℕ) (hL : 1440 ≤ n) (hU : n ≤ 1500) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4914 := by
  if h : n < 1450 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4914_range_1440_1500_chk_1440 n (by omega) h
  else
    if h : n < 1460 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4914_range_1440_1500_chk_1450 n (by omega) h
    else
      if h : n < 1470 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4914_range_1440_1500_chk_1460 n (by omega) h
      else
        if h : n < 1480 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4914_range_1440_1500_chk_1470 n (by omega) h
        else
          if h : n < 1490 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4914_range_1440_1500_chk_1480 n (by omega) h
          else
            if h : n < 1500 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4914_range_1440_1500_chk_1490 n (by omega) h
            else
              exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4914_range_1440_1500_chk_1500 n (by omega) (by omega)

end Commons.NumberTheory.Lagarias