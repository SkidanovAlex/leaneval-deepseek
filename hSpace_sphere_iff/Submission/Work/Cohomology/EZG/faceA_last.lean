import Mathlib
import Submission.Work.Cohomology.EZClassify

namespace Work.Cohomology.EZG

/-- Deleting the last position of a shuffle does not change `cnt` below the last vertex:
for a threshold `m ≤ N`, the elements counted below `m` never include `Fin.last N`. -/
lemma cnt_delPosP_last {N : ℕ} (A : Finset (Fin (N+1))) {m : ℕ} (hm : m ≤ N) :
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

theorem faceA_last {N P : ℕ} (A : Finset (Fin (N+1))) (hA : A.card ≤ P+1)
    (hN : (Fin.last N) ∈ A) :
    (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ (Fin.last (N+1))) (Work.Cohomology.shA A hA)) =
      (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.shA (Work.Cohomology.delPosP A (Fin.last N))
          (by rw [Work.Cohomology.delPosP_card hN]; omega))
        (SimplexCategory.δ (Fin.last (P+1)))) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    Work.Cohomology.shA_apply, Work.Cohomology.delta_toOrderHom, val_succAbove']
  have hjN : (j:ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  have h1 : ¬ ((Fin.last (N+1)).val ≤ (j:ℕ)) := by rw [Fin.val_last]; omega
  rw [if_neg h1, add_zero]
  have h2 : ¬ ((Fin.last (P+1)).val ≤ cnt (Work.Cohomology.delPosP A (Fin.last N)) (j:ℕ)) := by
    rw [Fin.val_last]
    have hc := Work.Cohomology.cnt_le_card (Work.Cohomology.delPosP A (Fin.last N)) (j:ℕ)
    have hd := Work.Cohomology.delPosP_card hN
    omega
  rw [if_neg h2]
  exact (cnt_delPosP_last A (by omega)).symm

end Work.Cohomology.EZG
