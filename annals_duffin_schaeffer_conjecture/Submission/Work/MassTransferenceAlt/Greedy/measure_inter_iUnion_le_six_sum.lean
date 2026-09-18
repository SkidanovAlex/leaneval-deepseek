import Mathlib
import Submission.Work.MassTransferenceAlt.Basic
import Submission.Work.MassTransferenceAlt.Greedy.exists_disjoint_subfamily

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace Work.MassTransferenceAlt.Greedy

open Work.MassTransferenceAlt

/-- **Covering bound for the enlarged intervals by a disjoint subfamily.**
Given a finite family of "enlarged" intervals `Fenl d c ρ i = Iv (c i) ((ρ i)^d)` with
`ρ i ≥ 0`, there is a pairwise disjoint subfamily `F ⊆ s` whose `3`-fold dilations cover
all the enlarged intervals of `s`.  Consequently the `1`-dimensional Hausdorff measure of
`J ∩ ⋃_{i ∈ s} Fenl d c ρ i` is at most `∑_{i ∈ F} 6 (ρ i)^d` (the length of the `3`-fold
dilation of `Fenl d c ρ i` is `6 (ρ i)^d`). -/
theorem measure_inter_iUnion_le_six_sum (d : ℝ) (c ρ : ℕ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (J : Set ℝ) (s : Finset ℕ) :
    ∃ F : Finset ℕ, F ⊆ s ∧
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j →
        Disjoint (Work.MassTransferenceAlt.Fenl d c ρ i) (Work.MassTransferenceAlt.Fenl d c ρ j)) ∧
      MeasureTheory.Measure.hausdorffMeasure 1 (J ∩ ⋃ i ∈ s, Work.MassTransferenceAlt.Fenl d c ρ i) ≤
        ∑ i ∈ F, ENNReal.ofReal (6 * (ρ i) ^ d) := by
  classical
  have hnr : ∀ i ∈ s, 0 ≤ (ρ i) ^ d := fun i _ => Real.rpow_nonneg (hρ i) d
  obtain ⟨G, hGsub, hGdisj, hGcov⟩ :=
    exists_disjoint_subfamily c (fun i => (ρ i) ^ d) s hnr
  refine ⟨G, hGsub, hGdisj, ?_⟩
  have hmono : J ∩ (⋃ i ∈ s, Work.MassTransferenceAlt.Fenl d c ρ i) ⊆
      ⋃ i ∈ G, Iv (c i) (3 * (ρ i) ^ d) := by
    rintro z ⟨_, hz⟩
    rw [Set.mem_iUnion₂] at hz ⊢
    obtain ⟨i, his, hzi⟩ := hz
    obtain ⟨j, hjG, hsub⟩ := hGcov i his
    exact ⟨j, hjG, hsub hzi⟩
  calc MeasureTheory.Measure.hausdorffMeasure 1
        (J ∩ ⋃ i ∈ s, Work.MassTransferenceAlt.Fenl d c ρ i)
      ≤ MeasureTheory.Measure.hausdorffMeasure 1 (⋃ i ∈ G, Iv (c i) (3 * (ρ i) ^ d)) :=
        measure_mono hmono
    _ ≤ ∑ i ∈ G, MeasureTheory.Measure.hausdorffMeasure 1 (Iv (c i) (3 * (ρ i) ^ d)) :=
        measure_biUnion_finset_le G _
    _ = ∑ i ∈ G, ENNReal.ofReal (6 * (ρ i) ^ d) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hausdorffMeasure_one_Iv (c i) (3 * (ρ i) ^ d)
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (hρ i) d))]
        congr 1
        ring

end Work.MassTransferenceAlt.Greedy
