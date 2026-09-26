import Mathlib
import Submission.Work.SG.SGprelude

namespace Work.SG

/-- Reducing `a` modulo `d` before adding `b` pointwise does not change the pointwise
reduction of `a + b` (in particular the lengths are unaffected, and truncation happens the
same way on both sides). -/
theorem zassoc_emodList_zipWith_add (d : ℕ) (a b : List ℤ) :
    emodList d (List.zipWith (· + ·) (emodList d a) b) = emodList d (List.zipWith (· + ·) a b) := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
      cases b with
      | nil => rfl
      | cons y ys =>
        simp only [emodList, List.zipWith_cons_cons, List.map_cons] at ih ⊢
        rw [ih]
        congr 1
        exact Int.emod_add_emod x d y

end Work.SG
