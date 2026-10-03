import Mathlib
import Submission.Work.Motion.pertSetup

/-!
# Derivative of the perturbation defect map `Fmap`

`Fmap τ m q w = (Tc q.1)^[m] (τ q.2 + w) - (Tc q.1)^[m] (τ q.2)` is the increment of the
`m`-th iterate of `Tc (q.1)` along the direction `w`, measured from the unperturbed point
`τ q.2`. Its `w`-derivative is the derivative `dTc m` of the iterate polynomial, evaluated
at the shifted point `(q.1, τ q.2 + w)`.

The parameter `τ` enters only through the *constant* `τ q.2`, so no differentiability
assumption on `τ` is required.
-/

namespace Work.Motion

open Work.Motion.Pert
open LeanEval.Dynamics.MandelbrotBoundary

theorem deriv_Fmap (τ : ℂ → ℂ) (m : ℕ) (q : ℂ × ℂ) (w : ℂ) :
    deriv (Work.Motion.Pert.Fmap τ m q) w = Work.Motion.Pert.dTc m (q.1, τ q.2 + w) := by
  -- `x ↦ TcIter m (q.1, x)` is the unperturbed iterate `(Tc q.1)^[m]`, whose derivative
  -- is `dTc m`, by definition of `dTc`.
  have hg : HasDerivAt (fun x : ℂ => TcIter m (q.1, x)) (dTc m (q.1, τ q.2 + w))
      (τ q.2 + w) := by
    have heq : (fun x : ℂ => TcIter m (q.1, x)) = fun y => (Tc q.1)^[m] y := by
      funext y; exact TcIter_eq m q.1 y
    rw [heq, ← deriv_TcIter m q.1 (τ q.2 + w)]
    exact ((differentiable_Tc q.1).iterate m).differentiableAt.hasDerivAt
  -- Translate by the constant `τ q.2` and subtract the constant value at `0`.
  have hshift : HasDerivAt (fun u : ℂ => τ q.2 + u) 1 w := by
    simpa using (hasDerivAt_id w).const_add (τ q.2)
  have h1 : HasDerivAt (fun u : ℂ => TcIter m (q.1, τ q.2 + u))
      (dTc m (q.1, τ q.2 + w) * 1) w := hg.comp w hshift
  have h2 : HasDerivAt (fun u : ℂ => TcIter m (q.1, τ q.2 + u) - TcIter m (q.1, τ q.2))
      (dTc m (q.1, τ q.2 + w) * 1) w :=
    h1.sub_const (TcIter m (q.1, τ q.2))
  rw [show Fmap τ m q = fun x => TcIter m (q.1, τ q.2 + x) - TcIter m (q.1, τ q.2) from rfl]
  simpa using h2.deriv

end Work.Motion
