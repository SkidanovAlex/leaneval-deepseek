import Mathlib
import Submission.Work.Diff.EXT.FlatPre

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- The `(j+1)`-st iterated derivative of `γ` at a point is, up to a fixed continuous linear
equivalence, the `j`-th iterated derivative of `fderiv γ` there; hence vanishing of the former
gives vanishing of the latter. -/
theorem iteratedFDeriv_fderiv_eq_zero
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ : ℝ × (Fin n → ℝ) → F} {j : ℕ} {x : ℝ × (Fin n → ℝ)}
    (h : iteratedFDeriv ℝ (j + 1) γ x = 0) :
    iteratedFDeriv ℝ j (fderiv ℝ γ) x = 0 := by
  -- `norm_iteratedFDeriv_fderiv` exhibits the `j`-th iterated derivative of `fderiv γ`
  -- as (the curried form of) the `(j+1)`-st iterated derivative of `γ`, so it suffices
  -- to observe that both have the same norm.
  rw [← norm_eq_zero, norm_iteratedFDeriv_fderiv, h, norm_zero]

end Work.Diff.EXT
