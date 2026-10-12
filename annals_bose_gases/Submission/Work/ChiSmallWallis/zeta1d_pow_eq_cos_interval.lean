import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.ChiSmall
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ChiSmallWallis

open MeasureTheory

lemma zeta1d_pow_eq_cos_interval (M : ℕ) (hM : 1 ≤ M) :
    ∫ y : ℝ, Submission.BoseGases.zeta1d y ^ (2*M)
      = ∫ x in (-(1/2):ℝ)..(1/2), Real.cos (Real.pi * x) ^ (2*M) := by
  have hpow : 2*M ≠ 0 := by omega
  have hfun : (fun y : ℝ => Submission.BoseGases.zeta1d y ^ (2*M))
      = (fun y : ℝ => (Set.Icc (-(1/2):ℝ) (1/2)).indicator
          (fun x => Real.cos (Real.pi * x) ^ (2*M)) y) := by
    funext y
    by_cases hy : y ∈ Set.Icc (-(1/2):ℝ) (1/2)
    · rw [Set.indicator_of_mem hy]
      exact congrArg (· ^ (2*M))
        (Submission.BoseGases.zeta1d_of_abs_le (by rw [Set.mem_Icc] at hy; rw [abs_le]; exact hy))
    · rw [Set.indicator_of_notMem hy]
      rw [Submission.BoseGases.zeta1d_of_one_half_lt
        (lt_of_not_ge (fun h => hy (Set.mem_Icc.mpr (abs_le.mp h)))), zero_pow hpow]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]

end Work.ChiSmallWallis
