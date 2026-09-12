import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace Commons.Probability.Levy

/-- The `level B` function of the level-set comparison lemma (Tikhomirov 2020) is
(Borel) measurable: it is a constant on the complementary rays, and on `[0,1]` it is
either identically `2` (when `w ≤ 0`) or a constant multiple of `√(1-s)/√w`. -/
lemma levelB_measurable (C w : ℝ) :
    Measurable (fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then (if 0 < w then C * Real.sqrt (1 - s) / Real.sqrt w else 2) else 0) := by
  classical
  by_cases hw : 0 < w
  · have hEq : (fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then (if 0 < w then C * Real.sqrt (1 - s) / Real.sqrt w else 2) else 0)
        = fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then C * Real.sqrt (1 - s) / Real.sqrt w else 0 := by
      funext s
      simp [hw]
    rw [hEq]
    refine Measurable.ite ?_ ?_ ?_
    · exact measurableSet_Icc
    · measurability
    · exact measurable_const
  · have hEq : (fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then (if 0 < w then C * Real.sqrt (1 - s) / Real.sqrt w else 2) else 0)
        = fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then (2 : ℝ) else 0 := by
      funext s
      simp [hw]
    rw [hEq]
    refine Measurable.ite ?_ ?_ ?_
    · exact measurableSet_Icc
    · exact measurable_const
    · exact measurable_const

end Commons.Probability.Levy