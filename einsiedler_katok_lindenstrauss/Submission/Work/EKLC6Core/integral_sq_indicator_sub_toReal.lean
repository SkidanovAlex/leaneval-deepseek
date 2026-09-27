import Mathlib

namespace Work.EKLC6Core

theorem integral_sq_indicator_sub_toReal {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν]
    (B : Set X) (hB : MeasurableSet B) :
    ∫ x, ((B.indicator (fun _ => (1 : ℝ))) x - (ν B).toReal)^2 ∂ν
      = (ν B).toReal * (1 - (ν B).toReal) := by
  set f : X → ℝ := B.indicator (fun _ => (1 : ℝ)) with hf
  set p : ℝ := (ν B).toReal with hp
  have hf_int : MeasureTheory.Integrable f ν := by
    rw [hf]; exact (MeasureTheory.integrable_const (1 : ℝ)).indicator hB
  have hint_f : ∫ x, f x ∂ν = p := by
    rw [hf, MeasureTheory.integral_indicator_const (1 : ℝ) hB]
    simp [MeasureTheory.Measure.real_def, hp]
  have hpt : ∀ x, (f x - p)^2 = f x * (1 - 2 * p) + p^2 := by
    intro x
    rw [hf]
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx]; ring
  calc ∫ x, (f x - p)^2 ∂ν
      = ∫ x, (f x * (1 - 2 * p) + p^2) ∂ν :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ x, f x * (1 - 2 * p) ∂ν + ∫ x, (p^2 : ℝ) ∂ν := by
        rw [MeasureTheory.integral_add (hf_int.mul_const _) (MeasureTheory.integrable_const _)]
    _ = (∫ x, f x ∂ν) * (1 - 2 * p) + p^2 := by
        rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real_def]
    _ = p * (1 - p) := by rw [hint_f]; ring

end Work.EKLC6Core
