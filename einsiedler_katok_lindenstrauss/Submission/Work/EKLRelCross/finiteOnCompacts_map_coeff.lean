import Mathlib
import Submission.Work.EKLRelCross.PeriodFunsDefs

namespace Work.EKLRelCross

open MeasureTheory
open Work.EKLContract

/-- The `(i,j)`-coordinate of a transvection is the transvection parameter. -/
private theorem coe_uij_entry' {i j : Fin 3} (hij : i ≠ j) (s : ℝ) :
    ((uij hij s : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = s := uij_coeff hij s

theorem finiteOnCompacts_map_coeff {i j : Fin 3} (hij : i ≠ j)
    (ν : MeasureTheory.Measure Work.EKLContract.SL3) [MeasureTheory.IsFiniteMeasureOnCompacts ν]
    (hν : ν (Set.range (fun t : ℝ => Work.EKLContract.uij hij t))ᶜ = 0) :
    MeasureTheory.IsFiniteMeasureOnCompacts
      (ν.map (fun g : Work.EKLContract.SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j)) := by
  refine ⟨fun K hK => ?_⟩
  have hcoe : Measurable (fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j) :=
    (continuous_coeff (i := i) (j := j)).measurable
  rw [Measure.map_apply hcoe hK.measurableSet]
  have hsubset : (fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j) ⁻¹' K ⊆
      (fun t : ℝ => uij hij t) '' K ∪ (Set.range (fun t : ℝ => uij hij t))ᶜ := by
    rintro g hg
    by_cases hr : g ∈ Set.range (fun t : ℝ => uij hij t)
    · obtain ⟨t, ht⟩ := hr
      left
      refine ⟨t, ?_, ht⟩
      have h1 : t = (g : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        have h2 := congrArg (fun x : SL3 => (x : Matrix (Fin 3) (Fin 3) ℝ) i j) ht
        rwa [coe_uij_entry' hij t] at h2
      rw [h1]; exact hg
    · exact Or.inr hr
  calc ν ((fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j) ⁻¹' K)
      ≤ ν ((fun t : ℝ => uij hij t) '' K ∪ (Set.range (fun t : ℝ => uij hij t))ᶜ) :=
        measure_mono hsubset
    _ ≤ ν ((fun t : ℝ => uij hij t) '' K) + ν ((Set.range (fun t : ℝ => uij hij t))ᶜ) :=
        measure_union_le _ _
    _ = ν ((fun t : ℝ => uij hij t) '' K) := by rw [hν, add_zero]
    _ < ⊤ := IsFiniteMeasureOnCompacts.lt_top_of_isCompact
        (hK.image (Work.EKLC7.continuous_uij hij))

end Work.EKLRelCross
