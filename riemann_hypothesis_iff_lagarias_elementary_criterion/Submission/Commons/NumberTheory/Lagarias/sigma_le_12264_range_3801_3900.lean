import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Submission.Commons.NumberTheory.SigmaCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Commons.NumberTheory.Lagarias

private theorem sigma_le_12264_range_3801_3900_chk_3801 :
    (List.range' 3801 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12264) = true := by
  decide +kernel

private theorem sigma_le_12264_range_3801_3900_chk_3811 :
    (List.range' 3811 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12264) = true := by
  decide +kernel

private theorem sigma_le_12264_range_3801_3900_chk_3821 :
    (List.range' 3821 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12264) = true := by
  decide +kernel

private theorem sigma_le_12264_range_3801_3900_chk_3831 :
    (List.range' 3831 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12264) = true := by
  decide +kernel

private theorem sigma_le_12264_range_3801_3900_chk_3841 :
    (List.range' 3841 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12264) = true := by
  decide +kernel

private theorem sigma_le_12264_range_3801_3900_chk_3851 :
    (List.range' 3851 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12264) = true := by
  decide +kernel

private theorem sigma_le_12264_range_3801_3900_chk_3861 :
    (List.range' 3861 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12264) = true := by
  decide +kernel

private theorem sigma_le_12264_range_3801_3900_chk_3871 :
    (List.range' 3871 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12264) = true := by
  decide +kernel

private theorem sigma_le_12264_range_3801_3900_chk_3881 :
    (List.range' 3881 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12264) = true := by
  decide +kernel

private theorem sigma_le_12264_range_3801_3900_chk_3891 :
    (List.range' 3891 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 12264) = true := by
  decide +kernel

theorem sigma_le_12264_range_3801_3900 (n : ℕ) (hL : 3801 ≤ n) (hU : n ≤ 3900) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 12264 := by
  if h : n < 3811 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12264_range_3801_3900_chk_3801 n (by omega) h
  else
    if h : n < 3821 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12264_range_3801_3900_chk_3811 n (by omega) h
    else
      if h : n < 3831 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12264_range_3801_3900_chk_3821 n (by omega) h
      else
        if h : n < 3841 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12264_range_3801_3900_chk_3831 n (by omega) h
        else
          if h : n < 3851 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12264_range_3801_3900_chk_3841 n (by omega) h
          else
            if h : n < 3861 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12264_range_3801_3900_chk_3851 n (by omega) h
            else
              if h : n < 3871 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12264_range_3801_3900_chk_3861 n (by omega) h
              else
                if h : n < 3881 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12264_range_3801_3900_chk_3871 n (by omega) h
                else
                  if h : n < 3891 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12264_range_3801_3900_chk_3881 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_12264_range_3801_3900_chk_3891 n (by omega) (by omega)

end Commons.NumberTheory.Lagarias