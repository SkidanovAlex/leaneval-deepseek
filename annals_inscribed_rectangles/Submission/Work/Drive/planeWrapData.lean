import Mathlib
import Submission.Work.Drive.WindingNumber

/-!
# The meridian (winding) input of the plane chart

`Submission/Work/Drive/PLANE_MERIDIAN_NOTES.md` proves that `Work.Drive.IsPlaneChart γ hγne Q` — the
existence of the capped-plane chart — **forces** the origin to be enclosed by `γ` with the *same sign*
as the turning of its tangent, i.e. `2 ε = 2 m` where `ε = ±1` is the Umlauf sign and `m` the position
winding.  Without that hypothesis the statement is *false* (the unit circle centred at `(2,0)` has
`m = 0`, `ε = 1`, and no plane chart).

This file supplies the hypothesis in the workspace's own vocabulary, without `winding` and without the
capping space:

* `Work.Drive.WrapData γ` — the doubled *position* direction of `γ` has a continuous lift whose total
  change over one period is non-zero ("the origin is enclosed, with the right orientation");
* `Work.Drive.circleP` — the parametrised unit circle `S¹ → ℂ`, used to state the topological core of
  the necessity argument (`Work.Drive.degree_circle_boundary_eq_zero`).

With `hU : Submission.Drive.UmlaufProp` the *proved*
`Work.Drive.doubled_position_total_eq_doubled_tangent_total` turns `WrapData γ` into `m = ε`, which is
exactly the condition under which the boundary `∂M` of the configuration band is a meridian of the cap
solid torus; the chart then exists (`Work.Drive.exists_planeChart`) and conversely cannot exist without
it (`Work.Drive.wrapData_of_planeChart`).
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- **The meridian input of the capping.**  The doubled position direction `x ↦ dirC (γ x)` of the
curve has a continuous lift whose total change over one period is non-zero.  Equivalently (by
`Work.Drive.total_change_of_position_lift`) the winding number of `γ` about the origin is non-zero:
the origin is enclosed by the curve.  This is the hypothesis that makes the boundary of the
configuration band a *meridian* of the cap solid torus, i.e. that the capped plane `M ∪ cap` exists. -/
def WrapData (γ : Circle → ℝ × ℝ) : Prop :=
  ∃ Ψ : ℝ → ℝ, Continuous Ψ ∧
    (∀ t : ℝ, ((Ψ t : ℝ) : UnitAddCircle) = Submission.Collision.dirC (γ (Circle.exp t))) ∧
    Ψ (2 * Real.pi) - Ψ 0 ≠ 0

/-- The parametrised unit circle `S¹ → ℂ`, i.e. `u ↦ e^{2π i u}` (the underlying point of the
`AddCircle (1 : ℝ)` element `u` in the unit circle of `ℂ`). -/
def circleP (u : UnitAddCircle) : ℂ := ((AddCircle.toCircle u : Circle) : ℂ)

/-- `circleP` is the exponential parametrisation: `circleP (t : UnitAddCircle) = e^{2π i t}`. -/
lemma circleP_coe (t : ℝ) :
    circleP (t : UnitAddCircle) = ((Circle.exp (2 * Real.pi * t) : Circle) : ℂ) := by
  rw [circleP, AddCircle.toCircle_apply_mk]
  norm_num

end

end Work.Drive
