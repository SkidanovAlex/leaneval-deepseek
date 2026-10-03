import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs

namespace Work.OROneRel

universe u

open Classical in
/-- The Magnus rewriting drops exactly the letters equal to `t`: its length is the number of
letters of `L` whose first component is not `t`. -/
theorem rewriteAux_length {α : Type u} (t : α) (i : ℤ) (L : List (α × Bool)) :
    (rewriteAux t i L).length = (L.filter (fun p => decide (p.1 ≠ t))).length := by
  induction L generalizing i with
  | nil => simp [rewriteAux.eq_def]
  | cons p L ih =>
    rw [rewriteAux.eq_def]
    by_cases hp : p.1 = t
    · simp only [hp, dif_pos]
      simp [ih, hp]
    · simp only [hp, dif_neg, not_false_eq_true]
      simp [List.length_cons, ih, hp]

theorem rewrite_length_lt {α : Type u} (t : α) {L : List (α × Bool)}
    (h : (t, true) ∈ L ∨ (t, false) ∈ L) :
    (Work.OROneRel.rewrite t L).length < L.length := by
  classical
  have hlen : (Work.OROneRel.rewrite t L).length =
      (L.filter (fun p => decide (p.1 ≠ t))).length := by
    unfold Work.OROneRel.rewrite
    exact rewriteAux_length t 0 L
  rw [hlen, ← List.countP_eq_length_filter, List.countP_lt_length_iff]
  rcases h with h | h
  · exact ⟨(t, true), h, by simp⟩
  · exact ⟨(t, false), h, by simp⟩

end Work.OROneRel
