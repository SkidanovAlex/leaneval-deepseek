import Mathlib
import Submission.Work.Cohomology.EZClassify

namespace Work.Cohomology.EZG

/-- The last `b`-face of the `b`-shuffle map: when the last position is not in the shuffle `A`,
deleting it and taking the last face of the smaller `b`-shuffle map commutes with taking the
last face followed by the `b`-shuffle map.  Both sides send a vertex `j : Fin (N+1)` to
`cntB A j.val`, which agrees with `cntB (delPosP A (Fin.last N)) j.val` below the deleted
position. -/
theorem faceB_last_g {N Q : ℕ} (A : Finset (Fin (N+1))) (hB : N + 1 ≤ A.card + (Q+1))
    (hcard : A.card = Q + 1) (hN : (Fin.last N) ∉ A) :
    (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ (Fin.last (N+1))) (Work.Cohomology.shB A hB)) =
      (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.shB (Work.Cohomology.delPosP A (Fin.last N))
          (by rw [Work.Cohomology.delPosP_card_of_notMem hN]; omega))
        (SimplexCategory.δ (Fin.last (Q+1)))) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    Work.Cohomology.shB_apply, Work.Cohomology.delta_toOrderHom]
  rw [Fin.succAbove_last_apply, Fin.succAbove_last_apply, Fin.val_castSucc, Fin.val_castSucc]
  exact (Work.Cohomology.EZG.cntB_delPosP_of_le A (Fin.last N) j.val (Fin.le_last j)).symm

end Work.Cohomology.EZG
