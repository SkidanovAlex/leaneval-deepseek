import Mathlib
import Submission.Commons.Probability.Levy.levy_interval_mass_bound

open MeasureTheory
open scoped ENNReal

namespace Commons.Probability.Levy

lemma levy_interval_L1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (w : ℝ), 0 < w → ∀ l : ℝ,
        (ν (Set.Icc (l - w) (l + w))).toReal ≤
          C * w * (∫ t in (-(1 / w))..(1 / w), ‖charFun ν t‖) := by
  refine ⟨16, by norm_num, ?_⟩
  intro ν hν w hw l
  have hmono : (ν (Set.Icc (l - w) (l + w))).toReal ≤
      (ν (Set.Icc (l - 2 * w) (l + 2 * w))).toReal := by
    have hsub : Set.Icc (l - w) (l + w) ⊆ Set.Icc (l - 2 * w) (l + 2 * w) := by
      intro x hx
      rw [Set.mem_Icc] at hx ⊢
      constructor <;> nlinarith
    exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hsub)
  calc
    (ν (Set.Icc (l - w) (l + w))).toReal
        ≤ (ν (Set.Icc (l - 2 * w) (l + 2 * w))).toReal := hmono
    _ = ν.real (Set.Icc (l - 2 * w) (l + 2 * w)) := by rw [Measure.real_def]
    _ ≤ 8 * (2 * w) * (∫ t in (-(2 / (2 * w)))..(2 / (2 * w)), ‖charFun ν t‖) :=
          levy_interval_mass_bound ν l (2 * w) (by positivity : 0 < 2 * w)
    _ = 16 * w * (∫ t in (-(1 / w))..(1 / w), ‖charFun ν t‖) := by
          have hwne : w ≠ 0 := ne_of_gt hw
          have hw2 : (2 : ℝ) / (2 * w) = 1 / w := by field_simp [hwne]
          rw [show 8 * (2 * w) = 16 * w by ring, hw2]

end Commons.Probability.Levy
