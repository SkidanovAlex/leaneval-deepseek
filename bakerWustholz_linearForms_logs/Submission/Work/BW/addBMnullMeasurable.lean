import Mathlib
import Submission.Work.BW.addBM_oneDim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory
open Pointwise
open scoped ENNReal

/-- Every nonempty null measurable subset of `ℝ` contains a nonempty *measurable* subset of the
same Lebesgue measure.  (Take a measurable subset of full measure from
`NullMeasurableSet.exists_measurable_subset_ae_eq` when the measure is nonzero; otherwise take a
singleton.)

This is the reduction that lets the `NullMeasurableSet` Brunn--Minkowski inequality be deduced
from the measurable version `Work.BW.addBM_oneDim`. -/
lemma exists_measurable_subset_nonempty_eq_measure {A : Set ℝ}
    (hA : NullMeasurableSet A volume) (hne : A.Nonempty) :
    ∃ A' ⊆ A, MeasurableSet A' ∧ A'.Nonempty ∧ volume A' = volume A := by
  by_cases h0 : volume A = 0
  · obtain ⟨a, ha⟩ := hne
    exact ⟨{a}, Set.singleton_subset_iff.mpr ha, measurableSet_singleton a, ⟨a, rfl⟩,
      by rw [h0]; exact measure_singleton a⟩
  · obtain ⟨A', hsub, hmeas, hae⟩ := hA.exists_measurable_subset_ae_eq
    refine ⟨A', hsub, hmeas, Set.nonempty_iff_ne_empty.mpr ?_, measure_congr hae⟩
    intro hemp
    exact h0 (by rw [← measure_congr hae, hemp, measure_empty])

theorem addBMnullMeasurable {A B : Set ℝ} (hA : NullMeasurableSet A volume)
    (hB : NullMeasurableSet B volume) (hAne : A.Nonempty) (hBne : B.Nonempty)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    volume (lam • A + (1 - lam) • B) ≥
      ENNReal.ofReal lam * volume A + ENNReal.ofReal (1 - lam) * volume B := by
  obtain ⟨A', hAsub, hAmeas, hAne', hAvol⟩ := exists_measurable_subset_nonempty_eq_measure hA hAne
  obtain ⟨B', hBsub, hBmeas, hBne', hBvol⟩ := exists_measurable_subset_nonempty_eq_measure hB hBne
  have hcore := addBM_oneDim hAne' hBne' hAmeas hBmeas h0 h1
  rw [hAvol, hBvol] at hcore
  refine le_trans hcore (measure_mono ?_)
  exact Set.add_subset_add (Set.smul_set_mono hAsub) (Set.smul_set_mono hBsub)

end Work.BW
