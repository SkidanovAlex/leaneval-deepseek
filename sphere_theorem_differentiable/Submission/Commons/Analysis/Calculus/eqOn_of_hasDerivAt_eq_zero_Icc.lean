import Mathlib.Analysis.Calculus.MeanValue

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Commons.Analysis.Calculus

/-- A function on a closed interval with vanishing derivative is constant. -/
theorem eqOn_of_hasDerivAt_eq_zero_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f 0 x) :
    ∀ x ∈ Set.Icc a b, f x = f a := by
  refine constant_of_has_deriv_right_zero (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x ⟨hx.1, le_of_lt hx.2⟩).hasDerivWithinAt)

end Commons.Analysis.Calculus