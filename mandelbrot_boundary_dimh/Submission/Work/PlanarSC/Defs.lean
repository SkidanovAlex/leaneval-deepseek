import Mathlib
import Submission.Lib.Unif2.Work.Spine.Plane.Dyadic

/-!
# Simple loops, and the `1`-periodic parametrisation of a closed curve

* `IsSimpleLoopIn γ`: a loop of a subset of `ℂ` is *simple* when, viewed as a closed curve in the
  plane, it is injective — two parameter values with the same image in `ℂ` are equal, unless they
  are the two endpoints of the parametrisation.
* `circleParam γ`: the standard `1`-periodic parametrisation `t ↦ γ (exp (2 π i t))` of a continuous
  map `γ : Circle → ℂ`, in terms of which the winding-number predicate
  `Commons.Topology.Winding.HasArg` of the library is phrased.
-/

namespace Work.PlanarSC

open Set

noncomputable section

/-- A loop `γ : Path x x` of `P ⊆ ℂ` is **simple** if it is injective on the parametrising circle:
two parameters with the same image in `ℂ` are equal, unless they are the two endpoints. -/
def IsSimpleLoopIn {P : Set ℂ} {x : ↥P} (γ : Path x x) : Prop :=
  ∀ s t : unitInterval, ((γ s : ↥P) : ℂ) = ((γ t : ↥P) : ℂ) →
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)

/-- The standard `1`-periodic parametrisation `t ↦ γ (exp (2 π i t))` of a closed curve
`γ` on the circle. -/
def circleParam (γ : C(Circle, ℂ)) (t : ℝ) : ℂ := γ (Circle.exp (2 * Real.pi * t))

@[simp]
theorem circleParam_apply (γ : C(Circle, ℂ)) (t : ℝ) :
    circleParam γ t = γ (Circle.exp (2 * Real.pi * t)) := rfl

/-- `circleParam γ` is `1`-periodic. -/
theorem circleParam_periodic (γ : C(Circle, ℂ)) : Function.Periodic (circleParam γ) 1 := by
  intro t
  have h : Circle.exp (2 * Real.pi * (t + 1)) = Circle.exp (2 * Real.pi * t) := by
    have h2 : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
    rw [h2]
    exact Circle.periodic_exp (2 * Real.pi * t)
  simp only [circleParam_apply, h]

end

end Work.PlanarSC
