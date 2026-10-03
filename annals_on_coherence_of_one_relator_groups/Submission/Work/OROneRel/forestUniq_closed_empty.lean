import Mathlib
import Submission.Work.OROneRel.delWordDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The decoration `decor c a L` of a word is empty exactly when the word is empty: it is a list of
the same length as `L`. -/
theorem decor_eq_nil {c : α → ℤ} {a : ℤ} {L : List (α × Bool)} :
    decor c a L = [] ↔ L = [] := by
  induction L generalizing a with
  | nil => simp [decor]
  | cons p L _ =>
    obtain ⟨x, b⟩ := p
    cases b <;> simp [decor]

/-- The sequence of traversed edges of the walk of `L` is empty exactly when `L` is empty. -/
theorem walkEdges_eq_nil_iff {c : α → ℤ} {a : ℤ} {L : List (α × Bool)} :
    walkEdges c a L = [] ↔ L = [] := by
  unfold walkEdges
  rw [List.map_eq_nil_iff]
  exact decor_eq_nil

/-- The empty walk is always a walk inside `T`. -/
theorem walkIn_nil (c : α → ℤ) (T : Set (α × ℤ)) (a : ℤ) : WalkIn c T a [] := by
  intro p hp
  simp [decor] at hp

/-- The empty walk has no immediate backtrack. -/
theorem noBT_nil (c : α → ℤ) (a : ℤ) : NoBT c a [] := by
  intro L₁ L₂ p q h
  exact (List.append_ne_nil_of_right_ne_nil L₁ (by simp) h.symm).elim

/-- A closed walk (`lsig c L = 0`) inside a forest `T` with no immediate backtrack is trivial.

Apply the uniqueness of non-backtracking paths to `L` and the empty walk `[]`, both running from `a`
to `a`: they have the same traversed edges up to reversal, i.e. `walkEdges c a L = []`, which by
`walkEdges_eq_nil_iff` forces `L = []`. -/
theorem forestUniq_closed_empty {α : Type u} (c : α → ℤ) (T : Set (α × ℤ))
    (hforest : ForestUniq c T) {a : ℤ} {L : List (α × Bool)}
    (h0 : lsig c L = 0) (hW : WalkIn c T a L) (hNoBT : NoBT c a L) : L = [] := by
  have hlsigL : lsig c L = a - a := by rw [h0]; ring
  have hlsigNil : lsig c [] = a - a := by simp [lsig]
  have hkey : walkEdges c a L = [] := by
    rcases hforest L [] a a hlsigL hW hNoBT hlsigNil (walkIn_nil c T a) (noBT_nil c a) with h | h
    · rw [h]; simp [walkEdges, decor]
    · rw [h]; simp [walkEdges, decor]
  exact walkEdges_eq_nil_iff.mp hkey

end Work.OROneRel
