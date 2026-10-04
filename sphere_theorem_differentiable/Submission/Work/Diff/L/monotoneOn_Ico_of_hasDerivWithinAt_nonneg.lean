import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

theorem monotoneOn_Ico_of_hasDerivWithinAt_nonneg {a T : ℝ} {f f' : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ico a T))
    (hf' : ∀ t ∈ Set.Ico a T, HasDerivWithinAt f (f' t) (Set.Ico a T) t)
    (h0 : ∀ t ∈ Set.Ico a T, 0 ≤ f' t) : MonotoneOn f (Set.Ico a T) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico a T) hf
    (fun x hx => (hf' x (interior_subset hx)).mono interior_subset)
    (fun x hx => h0 x (interior_subset hx))

end Work.Diff.L
