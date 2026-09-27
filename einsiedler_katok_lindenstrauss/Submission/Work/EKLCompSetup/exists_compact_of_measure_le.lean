import Mathlib
import Submission.Work.EKLComp.C8Defs

set_option linter.unusedVariables false

namespace Work.EKLCompSetup

/-- On a Polish space, a probability measure is inner regular with respect to compact sets:
if a measurable set `M` has measure at most `γ < 1`, then `Mᶜ` contains a compact set of
measure larger than any `r < 1 - γ`. -/
theorem exists_compact_of_measure_le
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    [PolishSpace Work.EKLContract.X3]
    {M : Set Work.EKLContract.X3} (hM : MeasurableSet M)
    {γ r : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hMγ : μ M ≤ ENNReal.ofReal γ) (hr0 : 0 ≤ r) (hr : r < 1 - γ) :
    ∃ K : Set Work.EKLContract.X3, IsCompact K ∧ K ⊆ Mᶜ ∧ ENNReal.ofReal r < μ K := by
  have hMcompl : MeasurableSet Mᶜ := hM.compl
  -- For a probability measure, `μ Mᶜ = 1 - μ M`.
  have hcompl : μ Mᶜ = 1 - μ M := by
    rw [MeasureTheory.measure_compl hM (MeasureTheory.measure_ne_top μ M),
      MeasureTheory.measure_univ]
  -- Hence `μ Mᶜ ≥ 1 - ofReal γ > ofReal r`.
  have hcompl_ge : 1 - ENNReal.ofReal γ ≤ μ Mᶜ := by
    rw [hcompl]
    exact tsub_le_tsub_left hMγ 1
  have hγ_lt_one : ENNReal.ofReal r < 1 - ENNReal.ofReal γ := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hγ0,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0]
    linarith [hr, hγ1]
  have hr_lt : ENNReal.ofReal r < μ Mᶜ := hγ_lt_one.trans_le hcompl_ge
  -- Inner regularity for compact sets gives a compact subset of `Mᶜ` of large measure.
  obtain ⟨K, hKM, hKc, hKr⟩ :=
    hMcompl.exists_lt_isCompact_of_ne_top (MeasureTheory.measure_ne_top μ Mᶜ) hr_lt
  exact ⟨K, hKc, hKM, hKr⟩

end Work.EKLCompSetup
