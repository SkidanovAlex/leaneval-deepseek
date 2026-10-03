import Mathlib
import Submission.Work.ORHughesFree.Tree.Log

/-!
# The weak order on finite rooted trees is a well-order

Every nonempty set of finite rooted trees has a least element for the weak order `le`
(`le x y` means `x = y` or `lt x y`).  Indeed `lt` is well founded (`lt_wf`), so a nonempty set `S`
has an element `t` minimal for `lt`; and `lt` is trichotomous (`lt_trichotomy`), so any `s ∈ S` is
either below, equal to, or above `t`, and the first alternative is excluded by minimality of `t`.
-/

namespace Work.ORHughesFree.Tree

/-- Every nonempty set of finite rooted trees has a least element with respect to `le`. -/
theorem exists_least (S : Set Work.ORHughesFree.Tree) (hS : S.Nonempty) :
    ∃ t ∈ S, ∀ s ∈ S, Work.ORHughesFree.Tree.le t s := by
  -- `lt` is well founded, so `S` contains an element minimal for the strict order.
  obtain ⟨t, htS, hmin⟩ := lt_wf.has_min S hS
  refine ⟨t, htS, fun s hs => ?_⟩
  -- `lt` is trichotomous, so `s` is comparable with the minimal element `t`.
  rcases lt_trichotomy t s with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact absurd h (hmin s hs)

end Work.ORHughesFree.Tree
