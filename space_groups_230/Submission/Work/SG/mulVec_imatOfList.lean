import Mathlib
import Submission.Work.SG.SGprelude

namespace Work.SG

/-- `Matrix.mulVec` of a cast flat matrix, componentwise. -/
theorem mulVec_imatOfList (a : List ℤ) (v : Fin 3 → ℝ) (i : Fin 3) :
    ((imatOfList a).map (Int.cast : ℤ → ℝ)).mulVec v i =
      ((List.finRange 3).map fun k => (a.getD (3 * i.val + k.val) 0 : ℝ) * v k).sum := by
  have hfin : List.finRange 3 = ([0, 1, 2] : List (Fin 3)) := rfl
  rw [hfin]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.map_apply, imatOfList,
    Matrix.of_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fin.val_zero,
    Fin.val_one, Fin.val_two]
  ring

end Work.SG
