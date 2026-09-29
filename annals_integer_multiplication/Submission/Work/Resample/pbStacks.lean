import Mathlib
import Submission.Work.Resample.pbDefs

/-!
# The auxiliary-stack description of the `progTensorB` invariant

The round invariant `Work.Resample.PBInv` of `progTensorB` describes the auxilary stacks 1–13 of the
program as explicit lists of values.  This file isolates that part of the invariant as
`Work.Resample.PBStacks`, so that the *frame cleanup* word (`Work.Resample.pbClr`) — which runs after
the epilogue and must empty every auxiliary stack — can be stated against it directly.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The auxiliary-stack description of `PBInv` at round `j` (stacks `1, …, 13`; value stacks). -/
def PBStacks (ss ts : List ℕ) (p α : ℕ) (M : Val) (j : ℕ) (a : Stk → List Val) : Prop :=
  a 1 = [] ∧ a 2 = [intList (ts.drop j)] ∧ a 3 = [intList (ss.drop j)] ∧
  a 4 = [.int α] ∧ a 5 = [.int p] ∧ a 6 = [.int ((ss.take j).prod)] ∧
  a 7 = [.int ((ts.drop j).prod)] ∧
  a 8 = [] ∧ a 9 = [] ∧ a 10 = [] ∧ a 11 = [] ∧ a 12 = [M] ∧ a 13 = [] ∧
  (∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} : Finset ℕ) →
    a k = [])

/-- `PBInv` implies the auxiliary-stack description `PBStacks`. -/
theorem PBStacks_of_PBInv (p α : ℕ) (ss ts : List ℕ) (Kb : ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (M : Val) (rest : List Val) (j : ℕ)
    {vs : List Val} {a : Stk → List Val}
    (h : PBInv p α ss ts Kb Φ zs0 M rest j vs a) : PBStacks ss ts p α M j a := by
  unfold PBInv at h
  exact h.2.2.2.2.2


/-- `PBStacks` only looks at the non-zero stacks, so it is invariant under a change of the
description of stack `0`. -/
theorem PBStacks_congr (ss ts : List ℕ) (p α : ℕ) (M : Val) (j : ℕ) {a a' : Stk → List Val}
    (h : PBStacks ss ts p α M j a) (h' : ∀ k : Stk, k ≠ 0 → a' k = a k) :
    PBStacks ss ts p α M j a' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h' 1 (by decide)]; exact h1
  · rw [h' 2 (by decide)]; exact h2
  · rw [h' 3 (by decide)]; exact h3
  · rw [h' 4 (by decide)]; exact h4
  · rw [h' 5 (by decide)]; exact h5
  · rw [h' 6 (by decide)]; exact h6
  · rw [h' 7 (by decide)]; exact h7
  · rw [h' 8 (by decide)]; exact h8
  · rw [h' 9 (by decide)]; exact h9
  · rw [h' 10 (by decide)]; exact h10
  · rw [h' 11 (by decide)]; exact h11
  · rw [h' 12 (by decide)]; exact h12
  · rw [h' 13 (by decide)]; exact h13
  · intro k hk hmem; rw [h' k hk]; exact h14 k hk hmem

end Work.Resample
