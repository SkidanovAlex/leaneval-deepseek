import Mathlib
import Submission.Work.Cohomology.EZClassify

namespace Work.Cohomology.EZG

/-- Deleting the last position of a shuffle does not change `cnt` below the last vertex:
for a threshold `m ≤ N` the elements of `A` counted below `m` are exactly the images under
`Fin.castSucc` of the elements of `delPosP A (Fin.last N)` counted below `m`. -/
lemma cnt_delPosP_last_B {N : ℕ} (A : Finset (Fin (N+1))) {m : ℕ} (hm : m ≤ N) :
    Work.Cohomology.cnt (Work.Cohomology.delPosP A (Fin.last N)) m = Work.Cohomology.cnt A m := by
  rw [Work.Cohomology.cnt, Work.Cohomology.cnt]
  have hset : A.filter (fun i : Fin (N+1) => i.val < m)
      = ((Work.Cohomology.delPosP A (Fin.last N)).filter (fun t : Fin N => t.val < m)).image
          Fin.castSucc := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro ⟨hiA, him⟩
      have hne : i ≠ Fin.last N := by
        intro h; rw [h, Fin.val_last] at him; omega
      refine ⟨i.castPred hne, ⟨?_, ?_⟩, ?_⟩
      · rw [Work.Cohomology.mem_delPosP, Fin.succAbove_last_apply, Fin.castSucc_castPred i hne]
        exact hiA
      · rw [Fin.coe_castPred]; exact him
      · rw [Fin.castSucc_castPred i hne]
    · rintro ⟨t, ⟨ht, htm⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rwa [Work.Cohomology.mem_delPosP, Fin.succAbove_last_apply] at ht
      · rw [Fin.val_castSucc]; exact htm
  rw [hset, Finset.card_image_of_injective _ (Fin.castSucc_injective N)]

theorem faceB_last {N P : ℕ} (A : Finset (Fin (N+1))) (hA : A.card ≤ P+1)
    (hN : (Fin.last N) ∉ A) :
    (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ (Fin.last (N+1))) (Work.Cohomology.shA A hA)) =
      (Work.Cohomology.shA (Work.Cohomology.delPosP A (Fin.last N))
          (by rw [Work.Cohomology.delPosP_card_of_notMem hN]; exact hA)) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    Work.Cohomology.shA_apply, Work.Cohomology.delta_toOrderHom]
  rw [Fin.succAbove_last_apply, Fin.val_castSucc]
  have hjN : (j:ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  exact (cnt_delPosP_last_B A hjN).symm

end Work.Cohomology.EZG
