import Mathlib
import Submission.Work.Cohomology.EZClassify
import Submission.Work.Cohomology.EZG.faceB_zero

namespace Work.Cohomology.EZG

/-- The `b`-count version of `cnt_delta_zero`: when `0 ∉ A`, counting the elements of the
complement of `A` below `m+1` counts the element `0` itself together with the successors of the
elements of the complement of `delPosP A 0` below `m`. -/
lemma cntB_delta_zero {N : ℕ} (A : Finset (Fin (N+1))) (h0 : (0 : Fin (N+1)) ∉ A)
    {m : ℕ} (hm : m ≤ N) :
    Work.Cohomology.cntB A (m + 1) = Work.Cohomology.cntB (Work.Cohomology.delPosP A 0) m + 1 := by
  rw [Work.Cohomology.cntB_eq_sub (A := A) (m := m + 1) (by omega),
      Work.Cohomology.cntB_eq_sub (A := Work.Cohomology.delPosP A 0) (m := m) hm]
  have hc : Work.Cohomology.cnt A (m + 1)
      = Work.Cohomology.cnt (Work.Cohomology.delPosP A 0) m := by
    have h := cnt_delta_zero A h0 (⟨m, by omega⟩ : Fin (N+1))
    rwa [Fin.succAbove_zero_apply, Fin.val_succ] at h
  rw [hc]
  have hle := Work.Cohomology.cnt_le_self (Work.Cohomology.delPosP A 0) hm
  omega

theorem faceB_zero_g {N Q : ℕ} (A : Finset (Fin (N+1))) (hB : N + 1 ≤ A.card + (Q+1))
    (h0 : (0 : Fin (N+1)) ∉ A) :
    (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ (0 : Fin (N+2))) (Work.Cohomology.shB A hB)) =
      (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.shB (Work.Cohomology.delPosP A 0)
          (by rw [Work.Cohomology.delPosP_card_of_notMem h0]; omega))
        (SimplexCategory.δ (0 : Fin (Q+2)))) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    Work.Cohomology.shB_apply, Work.Cohomology.delta_toOrderHom]
  rw [Fin.succAbove_zero_apply, Fin.succAbove_zero_apply]
  simp only [Fin.val_succ]
  exact cntB_delta_zero A h0 (m := ↑j) (Nat.lt_succ_iff.mp j.isLt)

end Work.Cohomology.EZG
