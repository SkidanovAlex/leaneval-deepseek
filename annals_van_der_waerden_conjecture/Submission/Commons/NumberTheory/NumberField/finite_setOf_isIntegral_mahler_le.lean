import Mathlib
import Submission.Commons.NumberTheory.NumberField.ncard_mahler_one_le

open NumberField NumberField.mixedEmbedding
open scoped Classical

namespace Commons.NumberTheory.NumberField

noncomputable section

theorem finite_setOf_isIntegral_mahler_le {K : Type*} [Field K] [NumberField K] (Y : ℝ) :
    ({a : K | IsIntegral ℤ a ∧
      (∏ w : NumberField.InfinitePlace K,
        (max 1 (NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K a))) ^ w.mult) ≤ Y}).Finite := by
  classical
  set T : Set (NumberField.mixedEmbedding.mixedSpace K) :=
    {x | ‖x‖ ≤ Y} ∩ (NumberField.mixedEmbedding.integerLattice K : Set _) with hT
  have hbdd : Bornology.IsBounded ({x : NumberField.mixedEmbedding.mixedSpace K | ‖x‖ ≤ Y}) := by
    rw [show {x : NumberField.mixedEmbedding.mixedSpace K | ‖x‖ ≤ Y}
        = Metric.closedBall 0 Y by
      ext x
      simp [Metric.mem_closedBall, dist_eq_norm]]
    exact Metric.isBounded_closedBall
  have hTfin : T.Finite := by
    rw [hT]
    rw [← NumberField.mixedEmbedding.span_latticeBasis K]
    exact ZSpan.setFinite_inter (NumberField.mixedEmbedding.latticeBasis K) hbdd
  have hsub : {a : K | IsIntegral ℤ a ∧
      (∏ w : NumberField.InfinitePlace K,
        (max 1 (NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K a))) ^ w.mult) ≤ Y}
      ⊆ NumberField.mixedEmbedding K ⁻¹' T := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha
    obtain ⟨hint, hM⟩ := ha
    simp only [Set.mem_preimage, hT, Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
      refine Finset.sup'_le Finset.univ_nonempty _ (fun w _ => ?_)
      exact le_trans (normAtPlace_le_mahlerK a w) hM
    · exact ⟨⟨a, hint⟩, rfl⟩
  exact Set.Finite.subset
    (hTfin.preimage (fun _ _ _ _ h => NumberField.mixedEmbedding_injective K h)) hsub

end

end Commons.NumberTheory.NumberField
