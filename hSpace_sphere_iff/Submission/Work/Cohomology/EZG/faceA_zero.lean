import Mathlib
import Submission.Work.Cohomology.EZClassify

namespace Work.Cohomology.EZG

/-- Counting the elements of `A` below `m+1`, when `0 ∈ A`: they are `0` itself together with the
successors of the elements of `delPosP A 0` below `m`. -/
lemma cnt_succ_zero {N : ℕ} (A : Finset (Fin (N+1))) (h0 : (0 : Fin (N+1)) ∈ A) (m : ℕ) :
    Work.Cohomology.cnt A (m+1) = Work.Cohomology.cnt (Work.Cohomology.delPosP A 0) m + 1 := by
  have hset : A.filter (fun i : Fin (N+1) => i.val < m+1)
      = insert 0 (((Work.Cohomology.delPosP A 0).filter (fun t : Fin N => t.val < m)).image
            Fin.succ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨hiA, hi⟩
      by_cases h : i = 0
      · exact Or.inl h
      · obtain ⟨t, ht⟩ := Fin.eq_succ_of_ne_zero h
        refine Or.inr ⟨t, ⟨?_, ?_⟩, ht.symm⟩
        · rw [Work.Cohomology.mem_delPosP, Fin.succAbove_zero_apply]
          rw [← ht]; exact hiA
        · rw [ht] at hi; simp only [Fin.val_succ] at hi; omega
    · rintro (rfl | ⟨t, ⟨htmem, htlt⟩, rfl⟩)
      · exact ⟨h0, by simp⟩
      · refine ⟨?_, ?_⟩
        · rw [Work.Cohomology.mem_delPosP, Fin.succAbove_zero_apply] at htmem
          exact htmem
        · simp only [Fin.val_succ]; omega
  rw [Work.Cohomology.cnt, Work.Cohomology.cnt, hset,
    Finset.card_insert_of_notMem (by
      intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨t, _, ht⟩ := hmem
      exact Fin.succ_ne_zero t ht),
    Finset.card_image_of_injective _ (fun a b hab => Fin.succ_inj.mp hab)]

theorem faceA_zero {N P : ℕ} (A : Finset (Fin (N+1))) (hA : A.card ≤ P+1)
    (h0 : (0 : Fin (N+1)) ∈ A) :
    (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ (0 : Fin (N+2))) (Work.Cohomology.shA A hA)) =
      (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.shA (Work.Cohomology.delPosP A 0)
          (by rw [Work.Cohomology.delPosP_card h0]; omega))
        (SimplexCategory.δ (0 : Fin (P+2)))) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    Work.Cohomology.shA_apply, Work.Cohomology.delta_toOrderHom]
  rw [Fin.succAbove_zero_apply, Fin.succAbove_zero_apply]
  simp only [Fin.val_succ]
  exact cnt_succ_zero A h0 ↑j

end Work.Cohomology.EZG
