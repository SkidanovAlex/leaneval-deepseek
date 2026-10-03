import Mathlib
import Submission.Work.Motion.pertSetup

namespace Work.Motion

open LeanEval.Dynamics.MandelbrotBoundary

/-- Chain rule for the `m`-th iterate of `Tc` composed with a differentiable parametrisation:
`deriv ((Tc c)^[m] ∘ τ) z = dTc m (c, τ z) * deriv τ z`. -/
theorem deriv_comp_TcIter (m : ℕ) (c : ℂ) {τ : ℂ → ℂ} {z : ℂ} (hτ : DifferentiableAt ℂ τ z) :
    deriv (fun y => Work.Motion.Pert.TcIter m (c, τ y)) z
      = Work.Motion.Pert.dTc m (c, τ z) * deriv τ z := by
  have hOuter : DifferentiableAt ℂ (fun x : ℂ => Pert.TcIter m (c, x)) (τ z) :=
    (Pert.differentiable_TcIter m).differentiableAt.comp (τ z)
      ((differentiableAt_const c).prodMk differentiableAt_id)
  have hfun : (fun y : ℂ => Pert.TcIter m (c, τ y))
      = (fun x : ℂ => Pert.TcIter m (c, x)) ∘ τ := rfl
  rw [hfun, deriv_comp z hOuter hτ]
  have h2 : (fun x : ℂ => Pert.TcIter m (c, x)) = (fun x : ℂ => (Tc c)^[m] x) := by
    funext x; exact Pert.TcIter_eq m c x
  rw [h2, Pert.deriv_TcIter]

end Work.Motion
