import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

namespace Work.ORBassSerre.Tree.Reduction

open Quiver

/-- In a graph, if there is a path from `a` to `b`, then there is a reduced path from `a` to `b`
(namely one of minimal length). -/
theorem qpath_exists_isReduced {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (h : Nonempty (Quiver.Path a b)) : ∃ p : Quiver.Path a b, p.IsReduced := by
  suffices ∀ n, ∀ {a b : V} (p : Quiver.Path a b), p.length = n →
      ∃ q : Quiver.Path a b, q.IsReduced by
    obtain ⟨p⟩ := h
    exact this p.length p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b p hp
    by_cases hred : p.IsReduced
    · exact ⟨p, hred⟩
    · rw [Quiver.Path.IsReduced] at hred
      push Not at hred
      obtain ⟨q, hq⟩ := hred
      have hlt : q.length < n := by rw [← hp]; exact hq.length_lt
      exact ih q.length hlt q rfl

end Work.ORBassSerre.Tree.Reduction
