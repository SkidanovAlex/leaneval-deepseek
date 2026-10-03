import Mathlib
import Submission.Work.ORBassSerre.Action.QuotientGroupOrbitV

namespace Work.ORBassSerre.QuotientTree

universe u

open Quiver

/-- An arrow between two orbits in the quotient graph `V ⧸ N` is the class of an arrow of `V`
between representatives. -/
theorem orbitQuiver_nonempty_hom_iff {G V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [GraphAction G V] (N : Subgroup G)
    [N.Normal] (A B : Work.ORBassSerre.orbitV N V) :
    Nonempty (A ⟶ B) ↔ ∃ (a b : V), (Quotient.mk'' a : Work.ORBassSerre.orbitV N V) = A ∧
      (Quotient.mk'' b : Work.ORBassSerre.orbitV N V) = B ∧ Nonempty (a ⟶ b) := by
  constructor
  · rintro ⟨E⟩
    obtain ⟨e, -, hl, hr⟩ := E.2
    exact ⟨e.left, e.right, hl, hr, ⟨e.hom⟩⟩
  · rintro ⟨a, b, ha, hb, ⟨f⟩⟩
    exact ⟨Quiver.homOfEq (Work.ORBassSerre.orbitArrow (G := N) f) ha hb⟩

end Work.ORBassSerre.QuotientTree
