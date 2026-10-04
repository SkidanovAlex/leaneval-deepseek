import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

theorem antitoneOn_Ico_of_hasDerivWithinAt_nonpos {a T : ℝ} {f f' : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ico a T))
    (hf' : ∀ t ∈ Set.Ico a T, HasDerivWithinAt f (f' t) (Set.Ico a T) t)
    (h0 : ∀ t ∈ Set.Ico a T, f' t ≤ 0) : AntitoneOn f (Set.Ico a T) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Ico a T) (f := f) (f' := f')
    (convex_Ico a T) hf ?_ ?_
  · intro x hx
    rw [interior_Ico] at hx ⊢
    exact (hf' x (Set.Ioo_subset_Ico_self hx)).mono Set.Ioo_subset_Ico_self
  · intro x hx
    rw [interior_Ico] at hx
    exact h0 x (Set.Ioo_subset_Ico_self hx)

end Work.Diff.L
