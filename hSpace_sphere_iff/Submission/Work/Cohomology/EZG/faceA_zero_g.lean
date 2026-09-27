import Mathlib
import Submission.Work.Cohomology.EZClassify

namespace Work.Cohomology.EZG

/-- When `0 ∈ A`, the number of elements of the complement of `A` that lie below `m+1` equals the
number of elements of the complement of `delPosP A 0` (the shuffle with the position `0` deleted)
that lie below `m`: the two sets correspond under `t ↦ Fin.succ t`. -/
lemma cntB_succ_zero {N : ℕ} (A : Finset (Fin (N+1))) (h0 : (0 : Fin (N+1)) ∈ A) (m : ℕ) :
    Work.Cohomology.cntB A (m+1) = Work.Cohomology.cntB (Work.Cohomology.delPosP A 0) m := by
  have hset : (Finset.univ \ A).filter (fun i : Fin (N+1) => i.val < m+1)
      = (((Finset.univ \ Work.Cohomology.delPosP A 0).filter
            (fun t : Fin N => t.val < m)).image Fin.succ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hiA, hi⟩
      have hne : i ≠ 0 := fun h => hiA (h ▸ h0)
      obtain ⟨t, ht⟩ := Fin.eq_succ_of_ne_zero hne
      refine ⟨t, ⟨?_, ?_⟩, ht.symm⟩
      · rw [Work.Cohomology.mem_delPosP, Fin.succAbove_zero_apply]
        rw [← ht]; exact hiA
      · rw [ht] at hi; simp only [Fin.val_succ] at hi; omega
    · rintro ⟨t, ⟨htmem, htlt⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Work.Cohomology.mem_delPosP, Fin.succAbove_zero_apply] at htmem
        exact htmem
      · simp only [Fin.val_succ]; omega
  rw [Work.Cohomology.cntB, Work.Cohomology.cntB, hset,
    Finset.card_image_of_injective _ (fun a b hab => Fin.succ_inj.mp hab)]

theorem faceA_zero_g {N Q : ℕ} (A : Finset (Fin (N+1))) (hB : N + 1 ≤ A.card + (Q+1))
    (h0 : (0 : Fin (N+1)) ∈ A) :
    (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ (0 : Fin (N+2))) (Work.Cohomology.shB A hB)) =
      (Work.Cohomology.shB (Work.Cohomology.delPosP A 0)
          (by rw [Work.Cohomology.delPosP_card h0]; omega)) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    Work.Cohomology.shB_apply, Work.Cohomology.delta_toOrderHom]
  rw [Fin.succAbove_zero_apply]
  simp only [Fin.val_succ]
  exact cntB_succ_zero A h0 ↑j

end Work.Cohomology.EZG
