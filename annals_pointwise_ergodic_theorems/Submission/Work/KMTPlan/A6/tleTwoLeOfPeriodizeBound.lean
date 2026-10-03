import Mathlib
import Submission.Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound
import Submission.Work.KMTAreas.A7.Large.Defs

namespace Work.KMTPlan.A6

theorem tleTwoLeOfPeriodizeBound (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.periodize φ ξ‖ ≤ M)
    (hmem : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure)
    (f : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tle ρ l φ f) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) * M)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  have hΦ : MeasureTheory.MemLp
      (Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ hmem
  have hnorm : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ) ξ‖
      ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) * M :=
    Work.Analysis.IonescuWainger.norm_iwSymbolSet_le _ hM
  have hCM : 0 ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) * M :=
    mul_nonneg (Nat.cast_nonneg _) hM0
  have key := eLpNorm_iwConv_two_le_of_symbol_bound
    (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
    (Work.Analysis.IonescuWainger.periodize φ)
    (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) * M) hCM hnorm hΦ f hf
  simpa only [Work.KMTAreas.A7.Tle] using key

end Work.KMTPlan.A6
