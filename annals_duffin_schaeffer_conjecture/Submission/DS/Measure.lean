import Mathlib
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Data.Real.Basic

open scoped ENNReal NNReal
open Set Filter MeasureTheory

/-!
# Measure-theoretic lemmas

Borel-Cantelli in the form needed, volume bounds of intervals, and countability
of the rationals.
-/

namespace Submission.DS

/-- The set `{x | |x - c| ≤ r}` is the closed ball around `c` of radius `r`. -/
lemma abs_sub_le_closedBall (c : ℝ) (r : ℝ≥0) :
    {x : ℝ | |x - c| ≤ (r : ℝ)} = Metric.closedBall c (r : ℝ) := by
  ext x
  change |x - c| ≤ (r : ℝ) ↔ x ∈ Metric.closedBall c (r : ℝ)
  rw [Metric.mem_closedBall]
  rw [Real.dist_eq]

/-- Borel-Cantelli over `ℕ+` for the `cofinite` filter, in terms of `Set.Infinite`. -/
lemma volume_infinite_mem_eq_zero {s : ℕ+ → Set ℝ} (hs : (∑' q : ℕ+, volume (s q)) ≠ ∞) :
    volume {x : ℝ | {q : ℕ+ | x ∈ s q}.Infinite} = 0 := by
  rw [← MeasureTheory.measure_limsup_cofinite_eq_zero (μ := volume) (s := s) hs]
  congr 1 with x
  rw [mem_limsup_iff_frequently_mem]
  exact frequently_cofinite_mem_iff_infinite.symm

/-- The volume of the part of a centred interval that lies in `[0,1]` is at most `2r`. -/
lemma volume_abs_sub_le (c : ℝ) (r : ℝ≥0) :
    volume ({x : ℝ | |x - c| ≤ (r : ℝ)} ∩ Set.Icc 0 1) ≤ ENNReal.ofReal (2 * (r : ℝ)) := by
  calc
    volume ({x : ℝ | |x - c| ≤ (r : ℝ)} ∩ Set.Icc 0 1)
        ≤ volume ({x : ℝ | |x - c| ≤ (r : ℝ)}) := measure_mono inter_subset_left
    _ = ENNReal.ofReal (2 * (r : ℝ)) := by
      rw [abs_sub_le_closedBall]
      simp

/-- Finite subadditivity for centred intervals with a common radius. -/
lemma volume_biUnion_interval_le (I : Finset ℕ) (c : ℕ → ℝ) (r : ℝ≥0) :
    volume ((⋃ a ∈ I, {x : ℝ | |x - c a| ≤ (r : ℝ)}) ∩ Set.Icc 0 1) ≤
      (I.card : ℝ≥0∞) * ENNReal.ofReal (2 * (r : ℝ)) := by
  calc
    volume ((⋃ a ∈ I, {x : ℝ | |x - c a| ≤ (r : ℝ)}) ∩ Set.Icc 0 1)
        ≤ volume (⋃ a ∈ I, {x : ℝ | |x - c a| ≤ (r : ℝ)}) := measure_mono inter_subset_left
    _ ≤ ∑ a ∈ I, volume {x : ℝ | |x - c a| ≤ (r : ℝ)} :=
          MeasureTheory.measure_biUnion_finset_le I (fun a => {x : ℝ | |x - c a| ≤ (r : ℝ)})
    _ = ∑ a ∈ I, ENNReal.ofReal (2 * (r : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [abs_sub_le_closedBall]
      simp
    _ = (I.card : ℝ≥0∞) * ENNReal.ofReal (2 * (r : ℝ)) := by
      rw [Finset.sum_const]
      exact nsmul_eq_mul _ _

/-- The rationals as a subset of `ℝ`. -/
def ratSet : Set ℝ := {x | ∃ q : ℚ, (q : ℝ) = x}

lemma ratSet_eq_range : ratSet = Set.range (fun q : ℚ => (q : ℝ)) := by
  ext x
  simp [ratSet]

lemma ratSet_countable : ratSet.Countable := by
  rw [ratSet_eq_range]
  exact Set.countable_range (fun q : ℚ => (q : ℝ))

lemma ratSet_measurableSet : MeasurableSet ratSet := by
  rw [ratSet_eq_range]
  exact (Set.countable_range (fun q : ℚ => (q : ℝ))).measurableSet

lemma ratSet_volume_zero : volume ratSet = 0 := by
  rw [ratSet_eq_range]
  exact (Set.countable_range (fun q : ℚ => (q : ℝ))).measure_zero volume

end Submission.DS
