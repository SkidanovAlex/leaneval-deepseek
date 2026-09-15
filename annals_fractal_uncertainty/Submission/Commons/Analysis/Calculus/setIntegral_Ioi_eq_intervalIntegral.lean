import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Calculus

open MeasureTheory

theorem setIntegral_Ioi_eq_intervalIntegral {g : ℝ → ℝ} {R : ℝ} (hR : 1 ≤ R)
    (h0 : ∀ t : ℝ, 0 < t → t < 1 → g t = 0) (hR2 : ∀ t : ℝ, R < t → g t = 0) :
    (∫ t in Set.Ioi (0 : ℝ), g t) = ∫ t in (1 : ℝ)..R, g t := by
  -- pointwise equality of the two indicator functions
  have hpiece : ∀ t : ℝ, (Set.Ioi (0 : ℝ)).indicator g t = (Set.Icc (1 : ℝ) R).indicator g t := by
    intro t
    by_cases ht : t ∈ Set.Icc (1 : ℝ) R
    · rw [Set.indicator_of_mem ht]
      have ht0 : t ∈ Set.Ioi (0 : ℝ) := by
        simp only [Set.mem_Ioi]; linarith [ht.1]
      rw [Set.indicator_of_mem ht0]
    · rw [Set.indicator_of_notMem ht]
      by_cases hI : t ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hI]
        simp only [Set.mem_Ioi] at hI
        rcases lt_or_ge t 1 with h1 | h1
        · exact h0 t hI h1
        · exact hR2 t (lt_of_not_ge fun hle => ht ⟨h1, hle⟩)
      · rw [Set.indicator_of_notMem hI]
  have step1 : (∫ t in Set.Ioi (0 : ℝ), g t) = ∫ t in Set.Icc (1 : ℝ) R, g t := by
    rw [← integral_indicator (measurableSet_Ioi (a := (0 : ℝ))),
      ← integral_indicator (measurableSet_Icc (a := (1 : ℝ)) (b := R))]
    apply integral_congr_ae
    filter_upwards with t using hpiece t
  have step2 : (∫ t in (1 : ℝ)..R, g t) = ∫ t in Set.Icc (1 : ℝ) R, g t := by
    rw [intervalIntegral.integral_of_le hR]
    exact setIntegral_congr_set (Ioc_ae_eq_Icc (a := (1 : ℝ)) (b := R))
  rw [step1, step2]

end Commons.Analysis.Calculus