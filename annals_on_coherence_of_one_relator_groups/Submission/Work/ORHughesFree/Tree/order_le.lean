import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs
import Submission.Work.ORHughesFree.Tree.order_good
import Submission.Work.ORHughesFree.Tree.order_wf

/-!
# The weak order on finite rooted trees

`le x y` means `x = y` or `x < y`.  We collect the order-theoretic axioms: reflexivity,
antisymmetry, transitivity, totality and well-foundedness of the strict part.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

theorem le_refl (x : Tree) : le x x := Or.inl rfl

theorem le_of_lt {x y : Tree} (h : lt x y) : le x y := Or.inr h

theorem lt_of_le_of_ne {x y : Tree} (h : le x y) (hne : x ≠ y) : lt x y :=
  h.resolve_left hne

theorem le_antisymm {x y : Tree} (hxy : le x y) (hyx : le y x) : x = y := by
  rcases hxy with hxy | hxy
  · exact hxy
  rcases hyx with hyx | hyx
  · exact hyx.symm
  · exact absurd hyx (lt_asymm hxy)

theorem le_trans {x y z : Tree} (hxy : le x y) (hyz : le y z) : le x z := by
  rcases hxy with hxy | hxy
  · rw [hxy]; exact hyz
  rcases hyz with hyz | hyz
  · rw [← hyz]; exact Or.inr hxy
  · exact Or.inr (lt_trans hxy hyz)

theorem le_total (x y : Tree) : le x y ∨ le y x := by
  rcases lt_trichotomy x y with h | h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem le_wf : WellFounded (fun x y : Tree => le x y ∧ x ≠ y) := by
  have h : (fun x y : Tree => le x y ∧ x ≠ y) = lt := by
    funext x y
    apply propext
    constructor
    · rintro ⟨h, hne⟩
      rcases h with h | h
      · exact absurd h hne
      · exact h
    · intro h
      exact ⟨Or.inr h, fun he => lt_irrefl (he ▸ h)⟩
  rw [h]
  exact lt_wf

end Work.ORHughesFree.Tree
