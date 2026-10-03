import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

namespace Work.ORBassSerre.Tree.Reduction

open Quiver

/-- Every path reduces, by deleting backtracks, to a reduced path. -/
theorem qpath_exists_reducesTo_isReduced {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {a b : V} (p : Quiver.Path a b) :
    ∃ q : Quiver.Path a b, p.ReducesTo q ∧ q.IsReduced := by
  -- Since deleting a backtrack strictly decreases the length, we argue by strong
  -- induction on the length of `p`.
  classical
  suffices h : ∀ n, ∀ {a b : V} (p : Quiver.Path a b), p.length = n →
      ∃ q : Quiver.Path a b, p.ReducesTo q ∧ q.IsReduced by
    exact h p.length p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b p hp
    by_cases hred : p.IsReduced
    · exact ⟨p, Relation.ReflTransGen.refl, hred⟩
    · -- `p` is not reduced, so some backtrack can be deleted.
      simp only [Quiver.Path.IsReduced, not_forall, not_not] at hred
      obtain ⟨q, hq⟩ := hred
      have hlen : q.length < n := by
        have := hq.length_lt
        omega
      obtain ⟨r, hr, hred'⟩ := ih q.length hlen q rfl
      exact ⟨r, Relation.ReflTransGen.head hq hr, hred'⟩

end Work.ORBassSerre.Tree.Reduction
