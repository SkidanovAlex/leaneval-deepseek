import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic

/-!
# PERT · `Work.Pert.EndDefect`: the defect at the lower end of the cylinder

For the perturbation data `(σ, α, u)` of `f z = z + z(z-σ)u z` the lift `F = liftF u σ α` is a
near-translation on the gate; the defect `d(w) = F w - (w+1)` is a function of `τ_f w` only,
namely (`1-s = (1+τu(τ)-σu(τ))/(1+τu(τ))`)

    d(w) = (1/(2πiα))·log(1 - σu(τ)/(1+τu(τ))) - 1 ,      τ = tauC σ α w .

As `Im (α w) → -∞` one has `τ → σ`, so the defect tends to the **end defect**

    D(σ) = (1/(2πiα))·log(1 - σu(σ)/(1+σu(σ))) - 1 = (1/(2πiα))·log(1/(1+σu(σ))) - 1 .

This is the "average defect per step" which the drift lemma `gate_walk_drift_explicit` must
compare against: the numerics (see
`Submission/Work/Pert/NOTES_gate_walk_drift_explicit_SESSION14.md`) show

    Σ_{j<n} d(w_j) = n·D(σ) + O(1+1/rr)      (w_{j+1} = F w_j)

so that the whole drift is governed by `D(σ)` and one uniformly bounded "coboundary" term.

Note `log(1/(1+σu(σ))) = log(1/(2-e^{2πiα} + σ(u(σ)-u(0))))` and `1/(2-e^{2πiα}) = 1+2πiα+O(α²)`,
so the principal logarithm is the correct branch and `D(σ) = O(‖α‖(1+1/rr))`.
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

/-- The defect at the lower end of the cylinder: the limit of `liftF u σ α w - (w+1)` as
`Im (α w) → -∞` (`τ → σ`), i.e. `(1/(2πiα)) log (1/(1+σ u σ)) - 1`. -/
def endDefect (u : ℂ → ℂ) (σ α : ℂ) : ℂ :=
  (1 / (2 * Real.pi * I * α)) * Complex.log (1 / (1 + σ * u σ)) - 1

end

end Work.Pert
