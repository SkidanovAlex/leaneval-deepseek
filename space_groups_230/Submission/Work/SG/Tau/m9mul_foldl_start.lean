import Mathlib
import Submission.Work.SG.sgTauDefs
import Submission.Work.SG.zassoc_m9mul_assoc

namespace Work.SG.Tau

/-!
# The fold identity `m9mul_foldl_start`

`wflatM gs w` (`sgTauDefs`) folds a word of generator indices through the flat matrix product
`m9mul`, starting from the flat identity `one9`.  The lemma below says that folding the same word
starting from any length-nine accumulator `A` gives the same result as multiplying `A` on the
left by the folded word.

The clean way to see this is to pass to the matrices denoted by the flat lists
(`imatOfList`): `imatOfList (m9mul a b) = imatOfList a * imatOfList b` and
`imatOfList one9 = 1`, so at the level of matrices the identity is associativity of the product.
Both sides of the goal are flat lists of length nine, so `imatOfList_inj` upgrades the matrix
identity back to the list identity.
-/

/-- Matrix-level form of the fold identity: for an *arbitrary* accumulator `A`, the matrix
denoted by the fold starting at `A` is the matrix of `A` times the matrix of the folded word. -/
theorem foldl_imatOfList (gs : List (List ℤ)) (w : List ℕ) (A : List ℤ) :
    imatOfList (w.foldl (fun a j => m9mul a (gs.getD j one9)) A)
      = imatOfList A * imatOfList (wflatM gs w) := by
  induction w generalizing A with
  | nil =>
      show imatOfList A = imatOfList A * imatOfList (wflatM gs ([] : List ℕ))
      rw [show wflatM gs ([] : List ℕ) = one9 from rfl,
        show imatOfList (one9 : List ℤ) = (1 : IMat) from imatOfList_one, mul_one]
  | cons j t ih =>
      have h1 : imatOfList (wflatM gs (j :: t))
          = imatOfList (gs.getD j one9) * imatOfList (wflatM gs t) := by
        show imatOfList (List.foldl (fun a j => m9mul a (gs.getD j one9))
              (m9mul one9 (gs.getD j one9)) t) = _
        rw [ih, imatOfList_mul,
          show imatOfList (one9 : List ℤ) = (1 : IMat) from imatOfList_one, one_mul]
      rw [List.foldl_cons, ih, h1, imatOfList_mul, Matrix.mul_assoc]

/-- The fold of a word of generator indices starting from a length-nine accumulator has length
nine (every `m9mul` does). -/
theorem foldl_length (gs : List (List ℤ)) (w : List ℕ) :
    ∀ A : List ℤ, A.length = 9 →
      (w.foldl (fun a j => m9mul a (gs.getD j one9)) A).length = 9 := by
  induction w with
  | nil => intro A hA; simpa using hA
  | cons j t ih =>
      intro A hA
      rw [List.foldl_cons]
      exact ih (m9mul A (gs.getD j one9)) (length_m9mul A _)

theorem m9mul_foldl_start (gs : List (List ℤ)) (w : List ℕ) {A : List ℤ} (hA : A.length = 9) :
    w.foldl (fun a j => m9mul a (gs.getD j one9)) A = m9mul A (wflatM gs w) := by
  refine imatOfList_inj (foldl_length gs w A hA) (length_m9mul A (wflatM gs w)) ?_
  rw [imatOfList_mul]
  exact foldl_imatOfList gs w A

end Work.SG.Tau
