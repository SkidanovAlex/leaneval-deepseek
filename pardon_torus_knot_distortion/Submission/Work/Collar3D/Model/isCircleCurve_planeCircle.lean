import Mathlib
import Submission.Work.Collar3D.Model.Defs

namespace Work.Collar3D.Model

/-- Injectivity of the standard parametrisation of the circle on one period `[0, 2π)`: the
coordinates `(cos θ, sin θ, 0)` determine `θ` there. -/
theorem injOn_planeCircle : Set.InjOn planeCircle (Set.Ico 0 (2 * Real.pi)) := by
  intro θ hθ θ' hθ' h
  obtain ⟨hθ0, hθ2⟩ := hθ
  obtain ⟨hθ'0, hθ'2⟩ := hθ'
  have hcos : Real.cos θ = Real.cos θ' := by
    have := congrArg (fun v : R3 => v 0) h
    simpa using this
  have hsin : Real.sin θ = Real.sin θ' := by
    have := congrArg (fun v : R3 => v 1) h
    simpa using this
  have hcos1 : Real.cos (θ - θ') = 1 := by
    rw [Real.cos_sub, hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq θ']
  have h1 : -(2 * Real.pi) < θ - θ' := by linarith
  have h2 : θ - θ' < 2 * Real.pi := by linarith
  exact sub_eq_zero.mp ((Real.cos_eq_one_iff_of_lt_of_lt h1 h2).mp hcos1)

/-- The parametrisation `θ ↦ (cos θ, sin θ, 0)` of the unit circle of the plane is a simple
closed curve in the sense of `Work.Collar3D.IsCircleCurve`. -/
theorem isCircleCurve_planeCircle : IsCircleCurve planeCircle :=
  ⟨continuous_planeCircle, periodic_planeCircle, injOn_planeCircle⟩

end Work.Collar3D.Model
