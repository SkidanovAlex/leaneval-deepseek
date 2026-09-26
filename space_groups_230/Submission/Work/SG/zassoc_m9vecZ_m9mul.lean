import Mathlib
import Submission.Work.SG.SGprelude

namespace Work.SG

/-- The flat list `v` read as a function `Fin 3 → ℤ` (out-of-range entries are `0`). -/
private def sgIvec (v : List ℤ) : Fin 3 → ℤ := fun i => v.getD i.val 0

/-- `m9vecZ` is the matrix–vector product of the flat matrix with the flat vector. -/
private lemma sgIvec_m9vecZ (a v : List ℤ) :
    sgIvec (m9vecZ a v) = (imatOfList a).mulVec (sgIvec v) := by
  funext i
  fin_cases i <;>
    simp [sgIvec, m9vecZ, imatOfList, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      List.range_succ]
  all_goals ring

/-- Reading a list entry as a `getD` at the same index. -/
private lemma sg_get_eq_getD (l : List ℤ) {n : ℕ} (h : n < l.length) :
    l.get ⟨n, h⟩ = l.getD n 0 :=
  (List.getD_eq_getElem l 0 h).symm

theorem zassoc_m9vecZ_m9mul (a b v : List ℤ) : m9vecZ (m9mul a b) v = m9vecZ a (m9vecZ b v) := by
  refine List.ext_get ?_ ?_
  · simp [m9vecZ]
  · intro n h1 h2
    have hn : n < 3 := by simpa [m9vecZ] using h1
    have hn2 : n < 3 := by simpa [m9vecZ] using h2
    rw [sg_get_eq_getD _ h1, sg_get_eq_getD _ h2]
    have key : sgIvec (m9vecZ (m9mul a b) v) ⟨n, hn⟩
        = sgIvec (m9vecZ a (m9vecZ b v)) ⟨n, hn2⟩ := by
      rw [sgIvec_m9vecZ, imatOfList_mul, ← Matrix.mulVec_mulVec, ← sgIvec_m9vecZ,
        ← sgIvec_m9vecZ]
    exact key

end Work.SG
