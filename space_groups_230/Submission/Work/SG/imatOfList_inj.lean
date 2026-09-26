import Mathlib
import Submission.Work.SG.SGprelude

namespace Work.SG

/-- A flat matrix (9 entries) is determined by the matrix it represents. -/
theorem imatOfList_inj {a b : List ℤ} (ha : a.length = 9) (hb : b.length = 9)
    (h : imatOfList a = imatOfList b) : a = b := by
  -- Compare entry `k` of both lists. It sits at row `k / 3`, column `k % 3` of the matrix.
  refine List.ext_getElem (by omega) ?_
  intro k h1 h2
  have hk : k < 9 := by omega
  have hh := congrFun (congrFun h ⟨k / 3, by omega⟩) ⟨k % 3, by omega⟩
  simp only [imatOfList, Matrix.of_apply] at hh
  have hk3 : 3 * (k / 3) + k % 3 = k := by omega
  rw [hk3, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hh
  exact hh

end Work.SG
