import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Submission.Commons.NumberTheory.SigmaCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Commons.NumberTheory.Lagarias

private theorem sigma_le_11904_range_3601_3700_chk_3601 :
    (List.range' 3601 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 11904) = true := by
  decide +kernel

private theorem sigma_le_11904_range_3601_3700_chk_3611 :
    (List.range' 3611 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 11904) = true := by
  decide +kernel

private theorem sigma_le_11904_range_3601_3700_chk_3621 :
    (List.range' 3621 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 11904) = true := by
  decide +kernel

private theorem sigma_le_11904_range_3601_3700_chk_3631 :
    (List.range' 3631 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 11904) = true := by
  decide +kernel

private theorem sigma_le_11904_range_3601_3700_chk_3641 :
    (List.range' 3641 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 11904) = true := by
  decide +kernel

private theorem sigma_le_11904_range_3601_3700_chk_3651 :
    (List.range' 3651 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 11904) = true := by
  decide +kernel

private theorem sigma_le_11904_range_3601_3700_chk_3661 :
    (List.range' 3661 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 11904) = true := by
  decide +kernel

private theorem sigma_le_11904_range_3601_3700_chk_3671 :
    (List.range' 3671 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 11904) = true := by
  decide +kernel

private theorem sigma_le_11904_range_3601_3700_chk_3681 :
    (List.range' 3681 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 11904) = true := by
  decide +kernel

private theorem sigma_le_11904_range_3601_3700_chk_3691 :
    (List.range' 3691 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 11904) = true := by
  decide +kernel

theorem sigma_le_11904_range_3601_3700 (n : ℕ) (hL : 3601 ≤ n) (hU : n ≤ 3700) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 11904 := by
  if h : n < 3611 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_11904_range_3601_3700_chk_3601 n (by omega) h
  else
    if h : n < 3621 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_11904_range_3601_3700_chk_3611 n (by omega) h
    else
      if h : n < 3631 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_11904_range_3601_3700_chk_3621 n (by omega) h
      else
        if h : n < 3641 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_11904_range_3601_3700_chk_3631 n (by omega) h
        else
          if h : n < 3651 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_11904_range_3601_3700_chk_3641 n (by omega) h
          else
            if h : n < 3661 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_11904_range_3601_3700_chk_3651 n (by omega) h
            else
              if h : n < 3671 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_11904_range_3601_3700_chk_3661 n (by omega) h
              else
                if h : n < 3681 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_11904_range_3601_3700_chk_3671 n (by omega) h
                else
                  if h : n < 3691 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_11904_range_3601_3700_chk_3681 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_11904_range_3601_3700_chk_3691 n (by omega) (by omega)

end Commons.NumberTheory.Lagarias