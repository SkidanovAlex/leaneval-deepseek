import Submission.CDTPlan.Interfaces

/-!
# cdt_linearIndependent — wave-2 contracts: the x-side lift of `φ_C` (orchestrator-owned)

`Φ(z) = (φ_C(z²) + √(φ_C(z²)(φ_C(z²) − 4)))/2` lifts `φ_C` through `y = x²/(x-1)`:
the two roots of `x² − y x + y = 0` at `y = φ_C(z²)` are `Φ(z)` and `Φ(−z)`.
-/

open Complex Metric

namespace Submission.CDTPlan

/-- A holomorphic lift `Φ` of `z ↦ φ_C(z²)` through `y = x²/(x−1)` with `w(Φ(z)) = Φ(−z)`. -/
def PhiLift : Prop :=
  ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ (ball 0 1) ∧
    (∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) ∧ Φ z * Φ (-z) = phiC (z ^ 2)) ∧
    (∀ z ∈ ball (0 : ℂ) 1, Φ z = 0 → z = 0)

end Submission.CDTPlan
