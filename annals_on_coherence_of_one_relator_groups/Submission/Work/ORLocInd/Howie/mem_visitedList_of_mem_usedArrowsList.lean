/-
# The endpoints of an arrow of a datum are visited vertices

Every arrow occurring in the datum `D` (an arrow of one of the closed paths `γ_j`, or an arrow of
one of the paths `δ_{j,k}` / relator paths `α_{j,k}` of a term, or the reverse of such an arrow)
joins two vertices that the datum visits: the arrow list of a path `p` consists of arrows between
consecutive vertices of `p`, hence both their ends occur in `p.vertices`.

This is the "vertex part" of the compatibility between the two lists of `Datum.lean` that make up
the span of a datum: `Datum.visitedList` (the vertices of the span) and `Datum.usedArrowsList`
(its arrows, as a subtype of `Quiver.Total V`).
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Span

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ORLocInd.Howie

open _root_.Quiver

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]

/-! ## The endpoints of an arrow of a path -/

/-- The tail (source) of an arrow occurring in a path is one of the vertices of the path. -/
private theorem left_mem_vertices_of_mem_arrowList {a b : V} {p : Quiver.Path a b}
    {e : Quiver.Total V} (h : e ∈ p.arrowList) : e.left ∈ p.vertices := by
  induction p with
  | nil => simp at h
  | cons q f ih =>
      rw [Quiver.Path.arrowList_cons, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · rw [Quiver.Path.vertices_cons, List.concat_eq_append]
        exact List.mem_append.mpr (Or.inl (ih h))
      · rw [h, Quiver.Path.vertices_cons, List.concat_eq_append]
        exact List.mem_append.mpr (Or.inl (Quiver.Path.end_mem_vertices q))

/-- The head (target) of an arrow occurring in a path is one of the vertices of the path. -/
private theorem right_mem_vertices_of_mem_arrowList {a b : V} {p : Quiver.Path a b}
    {e : Quiver.Total V} (h : e ∈ p.arrowList) : e.right ∈ p.vertices := by
  induction p with
  | nil => simp at h
  | cons q f ih =>
      rw [Quiver.Path.arrowList_cons, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · rw [Quiver.Path.vertices_cons, List.concat_eq_append]
        exact List.mem_append.mpr (Or.inl (ih h))
      · rw [h, Quiver.Path.vertices_cons, List.concat_eq_append]
        exact List.mem_append.mpr (Or.inr (by simp))

/-- Both endpoints of an arrow of a datum (i.e. of the list `Datum.rawArrows`, before passing to
the reverses) are visited by the datum. -/
private theorem mem_visitedList_of_mem_rawArrows {P : Presentation V} {v : V} {n : ℕ}
    (D : Datum P v n) {f : Quiver.Total V} (hf : f ∈ D.rawArrows) :
    f.left ∈ D.visitedList ∧ f.right ∈ D.visitedList := by
  rw [Datum.rawArrows, List.mem_append] at hf
  rcases hf with hf | hf
  · -- an arrow of one of the `γ_j`
    rw [List.mem_flatMap] at hf
    obtain ⟨j, -, hj⟩ := hf
    exact ⟨D.mem_visitedList_of_mem_gamma j (left_mem_vertices_of_mem_arrowList hj),
      D.mem_visitedList_of_mem_gamma j (right_mem_vertices_of_mem_arrowList hj)⟩
  · -- an arrow of one of the paths `δ` or relator paths `α` of a term
    rw [List.mem_flatMap] at hf
    obtain ⟨j, -, hf⟩ := hf
    rw [List.mem_flatMap] at hf
    obtain ⟨t, ht, hf⟩ := hf
    rw [List.mem_append] at hf
    rcases hf with hf | hf
    · exact ⟨D.mem_visitedList_of_mem_term_delta ht (left_mem_vertices_of_mem_arrowList hf),
        D.mem_visitedList_of_mem_term_delta ht (right_mem_vertices_of_mem_arrowList hf)⟩
    · exact ⟨D.mem_visitedList_of_mem_term_relator ht (left_mem_vertices_of_mem_arrowList hf),
        D.mem_visitedList_of_mem_term_relator ht (right_mem_vertices_of_mem_arrowList hf)⟩

/-- An arrow occurring in a datum joins two vertices visited by the datum.  (`usedArrowsList` is
`rawArrows` together with its reverses, and reversing an arrow swaps its endpoints.) -/
theorem mem_visitedList_of_mem_usedArrowsList {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [DecidableEq V] {P : Work.ORLocInd.Howie.Presentation V}
    {v : V} {n : ℕ} (D : Work.ORLocInd.Howie.Datum P v n) {e : Quiver.Total V}
    (h : e ∈ Work.ORLocInd.Howie.Datum.usedArrowsList D) :
    e.left ∈ Work.ORLocInd.Howie.Datum.visitedList D ∧
      e.right ∈ Work.ORLocInd.Howie.Datum.visitedList D := by
  rw [Datum.mem_usedArrowsList_iff] at h
  rcases h with h | h
  · exact mem_visitedList_of_mem_rawArrows D h
  · obtain ⟨h1, h2⟩ := mem_visitedList_of_mem_rawArrows D h
    exact ⟨by simpa using h2, by simpa using h1⟩

end Work.ORLocInd.Howie
