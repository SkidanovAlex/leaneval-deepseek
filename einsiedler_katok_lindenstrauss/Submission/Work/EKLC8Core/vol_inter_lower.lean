import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

open MeasureTheory
open scoped ENNReal

/-- **Lower bound for the measure of an intersection.**
For measurable `A, C ⊆ U` with `U` of finite measure,
`vol A + vol C - vol U ≤ vol (A ∩ C)`.

This is inclusion–exclusion together with monotonicity: from
`vol (A ∪ C) + vol (A ∩ C) = vol A + vol C` we get
`vol A + vol C - vol U ≤ vol A + vol C - vol (A ∪ C) = vol (A ∩ C)`,
because `A ∪ C ⊆ U` gives `vol (A ∪ C) ≤ vol U`. -/
theorem vol_inter_lower {A C U : Set ℝ} (hA : A ⊆ U) (hC : C ⊆ U)
    (hAm : MeasurableSet A) (hCm : MeasurableSet C) (hUm : MeasurableSet U)
    (hUfin : MeasureTheory.volume U ≠ ⊤) :
    Work.EKLC8Core.vol A + Work.EKLC8Core.vol C - Work.EKLC8Core.vol U ≤ Work.EKLC8Core.vol (A ∩ C) := by
  have hAf : (volume : Measure ℝ) A ≠ ⊤ := ne_top_of_le_ne_top hUfin (measure_mono hA)
  have hCf : (volume : Measure ℝ) C ≠ ⊤ := ne_top_of_le_ne_top hUfin (measure_mono hC)
  have hUAC : (A ∪ C) ⊆ U := Set.union_subset hA hC
  -- Inclusion–exclusion for the real-valued measure.
  have hie : vol (A ∪ C) + vol (A ∩ C) = vol A + vol C := by
    simpa only [vol_def, Measure.real_def] using
      measureReal_union_add_inter₀ (μ := (volume : Measure ℝ)) hCm.nullMeasurableSet hAf hCf
  -- Monotonicity of the real-valued measure.
  have hmono : vol (A ∪ C) ≤ vol U := by
    simpa only [vol_def, Measure.real_def] using
      measureReal_mono (μ := (volume : Measure ℝ)) hUAC hUfin
  linarith [hie, hmono]

end Work.EKLC8Core
