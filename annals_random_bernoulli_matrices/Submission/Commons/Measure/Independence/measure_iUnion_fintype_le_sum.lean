import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

namespace Commons.Measure.Independence

open MeasureTheory
open scoped ENNReal

/-- Finite union bound: for a finite family of sets, the measure of the union is at most the sum
of the measures (an `ENNReal`-valued statement, valid for arbitrary measures). -/
theorem measure_iUnion_fintype_le_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ι : Type*} [Fintype ι] (s : ι → Set Ω) :
    P (⋃ i, s i) ≤ ∑ i, P (s i) := by
  simpa using (MeasureTheory.measure_biUnion_finset_le (Finset.univ : Finset ι) s)

end Commons.Measure.Independence