import Mathlib
import Submission.Work.Cohomology.EZClassify

namespace Work.Cohomology.EZG

open CategoryTheory Simplicial Opposite

/-- The `0`-th face of the `a`-count of a shuffle `A` that omits `0`: since `0 ∉ A`, the count of
the elements of `A` strictly below `j + 1` equals the `a`-count of the shuffle `delPosP A 0`
obtained by deleting the position `0`.  (The last vertex is handled by `cnt_eq_card`.) -/
lemma cnt_delta_zero {N : ℕ} (A : Finset (Fin (N+1))) (h0 : (0 : Fin (N+1)) ∉ A)
    (j : Fin (N+1)) :
    cnt A (Fin.succAbove (0 : Fin (N+2)) j).val = cnt (delPosP A 0) j.val := by
  rcases Nat.lt_or_ge (j:ℕ) N with hj | hj
  · have h := EZG.cnt_succAbove A (0 : Fin (N+1)) (⟨j.val, hj⟩ : Fin N)
    have hv : (Fin.succAbove (0 : Fin (N+2)) j).val =
        (Fin.succAbove (0 : Fin (N+1)) (⟨j.val, hj⟩ : Fin N)).val := by
      rw [val_succAbove', val_succAbove']
      simp
    rw [hv, h]
    simp [h0]
  · have hjn : (j:ℕ) = N := by omega
    have hv : (Fin.succAbove (0 : Fin (N+2)) j).val = N + 1 := by
      rw [val_succAbove']; simp [hjn]
    rw [hv, hjn, cnt_eq_card A (le_refl (N+1)), cnt_eq_card (delPosP A 0) (le_refl N),
      delPosP_card_of_notMem h0]

theorem faceB_zero {N P : ℕ} (A : Finset (Fin (N+1))) (hA : A.card ≤ P+1)
    (h0 : (0 : Fin (N+1)) ∉ A) :
    (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ (0 : Fin (N+2))) (Work.Cohomology.shA A hA)) =
      (Work.Cohomology.shA (Work.Cohomology.delPosP A 0)
          (by rw [Work.Cohomology.delPosP_card_of_notMem h0]; exact hA)) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    shA_apply, delta_toOrderHom]
  exact cnt_delta_zero A h0 j

end Work.Cohomology.EZG
