import Mathlib
import Submission.Work.ORLyndon.powDefs

namespace Work.ORLyndon

theorem levelPart_finset_sum {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ) {ι : Type*} (s : Finset ι)
    (X : ι → MonoidAlgebra K (OneRelatorGroup r)) :
    Work.ORLyndon.levelPart t r u l hpow hσ i (∑ q ∈ s, X q) =
      ∑ q ∈ s, Work.ORLyndon.levelPart t r u l hpow hσ i (X q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Work.ORLyndon.levelPart_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Work.ORLyndon.levelPart_add, ih]

end Work.ORLyndon
