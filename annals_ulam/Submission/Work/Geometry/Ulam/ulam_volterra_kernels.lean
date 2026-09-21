import Mathlib
import Submission.Work.Geometry.Ulam.ulam_kernel

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped Interval ContDiff Topology

noncomputable section

/-- The state map `σ ↦ (x σ, y σ, x' σ, y' σ)` from the paper. -/
def ulamZ (x y : ℝ → ℝ) (σ : ℝ) : UlamState :=
  ![x σ, y σ, deriv x σ, deriv y σ]

/-- The averaged kernel `G₂(s,σ,z,z')` of the Abel-reduced equation:
`∫₀¹ K(s+τ(σ-s),σ,z,z') / √(τ(1-τ)) dτ`. -/
def ulamG2 (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : UlamState) : UlamState2 :=
  ∫ τ in (0 : ℝ)..1,
    (Real.sqrt (τ * (1 - τ)))⁻¹ • ulamK n h (s + τ * (σ - s)) σ z

/-- The first-argument derivative of `G₂`, used in the off-diagonal component of
the Volterra equation. -/
def ulamG2ds (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : UlamState) : UlamState2 :=
  deriv (fun u : ℝ => ulamG2 n h u σ z) s

/-- The off-diagonal Volterra kernel `Θ(s,σ,Z)`.  Its first two components are
`-x', -y'`, and its last two are `-∂G₂/∂s`. -/
def ulamTheta (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : UlamState) : UlamState :=
  ![ - (z 2), - (z 3), - (ulamG2ds n h s σ z) 0, - (ulamG2ds n h s σ z) 1]

/-- Coordinate form of `ulamTheta`. -/
lemma ulamTheta_apply (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : UlamState) :
    (ulamTheta n h s σ z) 0 = - (z 2) ∧
    (ulamTheta n h s σ z) 1 = - (z 3) ∧
    (ulamTheta n h s σ z) 2 = - (ulamG2ds n h s σ z) 0 ∧
    (ulamTheta n h s σ z) 3 = - (ulamG2ds n h s σ z) 1 := by
  simp [ulamTheta]

end

end Commons.Geometry.Ulam
