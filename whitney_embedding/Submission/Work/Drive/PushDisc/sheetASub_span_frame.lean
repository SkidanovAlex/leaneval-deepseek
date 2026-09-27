import Mathlib
import Submission.Work.Drive.PushDisc.sheetModel
import Submission.Work.Drive.PushDisc.milnorLens

namespace Work.Drive.PushDisc

/-- The model sheet `sheetA` (the `(x, u)`-coordinate plane of `Mdl k`) is spanned by the constant
vector `(1, 0, 0, 0)` together with the standard `u`-frame `ιu i = (0, 0, eᵢ, 0)`. -/
theorem sheetASub_span_frame (k : ℕ) :
    Work.Drive.PushDisc.sheetASub k
      = Submodule.span ℝ (Set.range (Fin.cons ((1 : ℝ), 0, 0, 0)
          (Work.Drive.PushDisc.iotaU k))) := by
  refine le_antisymm ?_ ?_
  · -- every element of the sheet is `x • (1,0,0,0) + ∑ uᵢ • ιuᵢ`
    intro ξ hξ
    rw [Work.Drive.PushDisc.mem_sheetASub] at hξ
    obtain ⟨hb, hv⟩ := hξ
    have hmem : ∀ u : EuclideanSpace ℝ (Fin k),
        ((0 : ℝ), 0, u, (0 : EuclideanSpace ℝ (Fin k)))
          ∈ Submodule.span ℝ (Set.range (Fin.cons ((1 : ℝ), 0, 0, 0)
              (Work.Drive.PushDisc.iotaU k))) := by
      intro u
      rw [← Work.Drive.PushDisc.sum_smul_iotaU k u]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Fin.succ i, by simp [Fin.cons_succ]⟩)
    have hdec : ξ = ξ.1 • ((1 : ℝ), 0, 0, 0) + (0, 0, ξ.2.2.1, 0) := by
      refine Work.Drive.PushDisc.mdl_ext ?_ ?_ ?_ ?_ <;> simp [hb, hv]
    rw [hdec]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp [Fin.cons_zero]⟩))
      (hmem ξ.2.2.1)
  · -- conversely each generator lies in the sheet
    refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    rw [SetLike.mem_coe, Work.Drive.PushDisc.mem_sheetASub]
    simp only [Work.Drive.Whitney.sheetA, Set.mem_ofPred_eq]
    induction i using Fin.cases with
    | zero => simp [Fin.cons_zero]
    | succ j => simp [Fin.cons_succ, Work.Drive.PushDisc.iotaU, Work.Drive.PushDisc.uPart]

end Work.Drive.PushDisc
