import Mathlib

namespace Work.RadialSpace

/-- The derivative of a real function, composed with the embedding `ℝ → ℂ`, is the
complexification of the derivative. -/
lemma deriv_ofReal_comp (h : ℝ → ℝ) (x : ℝ) :
    deriv (fun y : ℝ => ((h y : ℝ) : ℂ)) x = ((deriv h x : ℝ) : ℂ) := by
  by_cases hd : DifferentiableAt ℝ h x
  · exact hd.hasDerivAt.ofReal_comp.deriv
  · have hdH : ¬ DifferentiableAt ℝ (fun y : ℝ => ((h y : ℝ) : ℂ)) x := by
      intro hH
      exact hd ((Complex.reCLM.differentiableAt).comp x hH)
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hdH]
    simp

theorem iteratedDeriv_ofReal (m : ℕ) (g : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv m (fun y : ℝ => ((g y : ℝ) : ℂ)) x = ((iteratedDeriv m g x : ℝ) : ℂ) := by
  induction m generalizing x with
  | zero => simp [iteratedDeriv]
  | succ m ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    rw [show iteratedDeriv m (fun y : ℝ => ((g y : ℝ) : ℂ))
          = fun y : ℝ => ((iteratedDeriv m g y : ℝ) : ℂ) from funext ih]
    exact deriv_ofReal_comp _ x

end Work.RadialSpace
