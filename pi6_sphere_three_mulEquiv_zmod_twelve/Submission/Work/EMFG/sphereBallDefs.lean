import Mathlib

/-!
# The cone over an intersection of small balls on the unit sphere

A point `a` of the unit sphere of a real inner product space `E`, and a radius `ε`, determine the
open ball `Metric.ball a ε` in the sphere (with the chordal metric inherited from `E`).  For
`‖x‖ = 1` membership in that ball is equivalent to the *linear* inequality
`1 - ε²/2 < ⟪x, a⟫`, so an intersection of such balls is the trace on the sphere of an open
convex cone.  This file records that cone and the elementary bridge between the two descriptions.
-/

namespace Work.EMFG

open Set Metric

/-- A point of the unit sphere has norm one. -/
lemma norm_eq_one_of_mem_sphere {E : Type*} [SeminormedAddCommGroup E] {z : E}
    (hz : z ∈ Metric.sphere (0 : E) 1) : ‖z‖ = 1 := by
  rwa [Metric.mem_sphere, dist_zero_right] at hz

/-- The open cone over the intersection `⋂ i ∈ S, Metric.ball (a i) ε` of the unit sphere: the
set of those `x` whose normalisation `‖x‖⁻¹ • x` lies in the intersection.  It is described here,
equivalently, by the linear inequalities `(1 - ε²/2) * ‖x‖ < ⟪x, a i⟫`. -/
def ballCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α : Type*}
    (S : Finset α) (a : α → Metric.sphere (0 : E) 1) (ε : ℝ) : Set E :=
  {x | ∀ i ∈ S, (1 - ε ^ 2 / 2) * ‖x‖ < inner ℝ x (a i : E)}

end Work.EMFG
