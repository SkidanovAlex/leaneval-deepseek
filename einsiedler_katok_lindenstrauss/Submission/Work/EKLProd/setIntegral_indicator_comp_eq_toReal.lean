import Mathlib

open MeasureTheory

namespace Work.EKLProd

/-- The integral over a set `T` of the composition of the indicator of `S` with a function `g`
equals the (real) measure of `T ∩ g ⁻¹' S`. -/
theorem setIntegral_indicator_comp_eq_toReal {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : MeasureTheory.Measure α} {g : α → β} (hg : Measurable g) {S : Set β} (hS : MeasurableSet S)
    (T : Set α) :
    ∫ u in T, S.indicator (fun _ => (1 : ℝ)) (g u) ∂ν = (ν (T ∩ g ⁻¹' S)).toReal := by
  have hA : MeasurableSet (g ⁻¹' S) := hS.preimage hg
  have hfun : (fun u => S.indicator (fun _ => (1 : ℝ)) (g u)) =
      (fun u => (g ⁻¹' S).indicator (fun _ => (1 : ℝ)) u) := by
    funext u
    by_cases h : u ∈ g ⁻¹' S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.mp h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (fun hc => h (Set.mem_preimage.mpr hc))]
  rw [hfun, integral_indicator_const (1 : ℝ) hA]
  rw [measureReal_def, Measure.restrict_apply hA, Set.inter_comm]
  simp

end Work.EKLProd
