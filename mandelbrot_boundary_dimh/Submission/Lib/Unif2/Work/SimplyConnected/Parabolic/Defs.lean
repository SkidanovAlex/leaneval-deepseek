import Mathlib
import Submission.Lib.Unif2.Holomorphic

/-!
# Definitions for the local boundedness of normalised univalent families

The family of "normalised univalent maps" used in the parabolic case of the uniformization
theorem (Hubbard, *Teichmüller theory* Vol. 1, Chapter 1; Anghel–Bruin–Stan, Appendix AC) and the
set of points where such a family is uniformly bounded on a *neighbourhood*.
-/

namespace Work.SimplyConnected.Parabolic

open scoped Topology Manifold ContDiff
open Filter Metric Set

/-- The universal growth bound for normalised univalent functions on the unit disc, as a property
of a constant `C`. -/
def HasGrowthBound (C : ℝ) : Prop :=
  0 < C ∧ ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
    Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ + 1 ≤ ((1 + ‖z‖) / (1 - ‖z‖)) ^ C

/-- **The family is uniformly bounded on `V`**: one constant `B ≥ 0` bounds *every* member of the
family of normalised univalent maps on all of `V`. -/
def IsUnifBddOn {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x₀ : X) (U : Set X) (V : Set X) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ ⦃Ω : Set X⦄, IsOpen Ω → IsConnected Ω → U ⊆ Ω →
    ∀ (ψ : X → ℂ), (∀ x ∈ Ω, Submission.HolomorphicOnXAt ψ x) → Set.InjOn ψ Ω →
      ψ x₀ = 0 → deriv (ψ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1 →
      ∀ x ∈ V, ‖ψ x‖ ≤ B

/-- The set of points of `X` possessing an open neighbourhood, contained in `U`, on which the
family is uniformly bounded. -/
def goodSet {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x₀ : X) (U : Set X) : Set X :=
  {z : X | ∃ V : Set X, IsOpen V ∧ V ⊆ U ∧ z ∈ V ∧ IsUnifBddOn x₀ U V}

end Work.SimplyConnected.Parabolic
