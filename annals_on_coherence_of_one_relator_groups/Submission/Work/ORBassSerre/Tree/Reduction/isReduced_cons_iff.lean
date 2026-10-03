import Mathlib
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced

namespace Work.ORBassSerre.Tree.Reduction

open Quiver

/-- `p.cons e` is reduced iff `p` is reduced and the arrow `e` does not cancel with the last
arrow of `p` (i.e. `e` is not the reverse of the final arrow of `p`).  A backtrack deleted from
`p.cons e` either lives inside `p` or is exactly the one at the junction between `p` and `e`,
which is the content of `Tree.Map.deleteBacktrack_cons_iff`. -/
theorem isReduced_cons_iff {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c) : (p.cons e).IsReduced ↔ p.IsReduced ∧ ∀ (p' : Quiver.Path a c) (e' : c ⟶ b), p = p'.cons e' → e ≠ Quiver.reverse e' := by
  constructor
  · intro h
    refine ⟨fun r₀ hr₀ => ?_, fun p' e' hp he => ?_⟩
    · exact h (r₀.cons e)
        ((Tree.Map.deleteBacktrack_cons_iff p e (r₀.cons e)).mpr (Or.inl ⟨r₀, hr₀, rfl⟩))
    · exact h p'
        ((Tree.Map.deleteBacktrack_cons_iff p e p').mpr (Or.inr ⟨p', e', hp, he, rfl⟩))
  · rintro ⟨hp, hlast⟩ r hr
    rcases (Tree.Map.deleteBacktrack_cons_iff p e r).mp hr with ⟨r₀, hr₀, -⟩ | ⟨p', e', hp', he', -⟩
    · exact hp r₀ hr₀
    · exact hlast p' e' hp' he'

end Work.ORBassSerre.Tree.Reduction
