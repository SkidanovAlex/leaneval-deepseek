import Mathlib

namespace Work.EKLComp

theorem measure_eq_one_of_measureReal_eq_one {α : Type*} [MeasurableSpace α]
    {ν : MeasureTheory.Measure α} {s : Set α} (h : ν.real s = 1) : ν s = 1 := by
  rw [MeasureTheory.Measure.real] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

end Work.EKLComp
