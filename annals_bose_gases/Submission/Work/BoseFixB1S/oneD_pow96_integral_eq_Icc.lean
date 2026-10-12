import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.conv48Consts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open Submission.BoseGases

/-- `ζ(s)^96` and `cos(π s)^96` agree on `[-1/2, 1/2]` (where `ζ = cos(π·)`) and `ζ`
vanishes off it, so the full-line integral of `ζ^96` is the integral of `cos(π·)^96`
over `[-1/2, 1/2]`. -/
theorem oneD_pow96_integral_eq_Icc : (∫ s : ℝ, Submission.BoseGases.zeta1d s ^ 96) = ∫ s in Set.Icc (-(1 / 2) : ℝ) (1 / 2), Real.cos (Real.pi * s) ^ 96 := by
  have hpoint : ∀ s : ℝ, Submission.BoseGases.zeta1d s ^ 96
      = (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator
          (fun s => Real.cos (Real.pi * s) ^ 96) s := by
    intro s
    by_cases hs : s ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
    · rw [Set.indicator_of_mem hs]
      have habs : |s| ≤ 1 / 2 := abs_le.mpr (Set.mem_Icc.mp hs)
      rw [zeta1d_of_abs_le habs]
    · rw [Set.indicator_of_notMem hs]
      have habs : 1 / 2 < |s| := by
        by_contra hle
        exact hs (abs_le.mp (not_lt.mp hle))
      rw [zeta1d_of_one_half_lt habs, zero_pow (by norm_num : (96 : ℕ) ≠ 0)]
  calc (∫ s : ℝ, Submission.BoseGases.zeta1d s ^ 96)
      = ∫ s : ℝ, (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator
          (fun s => Real.cos (Real.pi * s) ^ 96) s :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ s in Set.Icc (-(1 / 2) : ℝ) (1 / 2), Real.cos (Real.pi * s) ^ 96 :=
        integral_indicator measurableSet_Icc

end Work.BoseFixB1S
