import Mathlib.Analysis.Real.Sqrt

namespace Commons.Probability.Levy

lemma levelB_nonneg (C w : ℝ) (hC : 0 ≤ C) :
    ∀ s : ℝ, 0 ≤ (fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then (if 0 < w then C * Real.sqrt (1 - s) / Real.sqrt w else 2) else 0) s := by
  intro s
  by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
  · by_cases hw : 0 < w
    · have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg (1 - s)
      have hprod : 0 ≤ C * Real.sqrt (1 - s) := mul_nonneg hC hsqrt_nonneg
      have hsqrt_pos : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
      have hmain : 0 ≤ C * Real.sqrt (1 - s) / Real.sqrt w :=
        div_nonneg hprod hsqrt_pos.le
      simpa [hs, hw] using hmain
    · norm_num [hs, hw]
  · norm_num [hs]

end Commons.Probability.Levy