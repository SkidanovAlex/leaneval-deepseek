import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The rotation carrying one unit vector to another: the formula

For unit vectors `u`, `e` of `ℝⁿ = EuclideanSpace ℝ (Fin n)` with `u ≠ -e`, the map

`rotMap u e x = x + ⟪x,u⟫ • (e - u) - (⟪x,e⟫ - ⟪x,u⟫ * ⟪u,e⟫)/(1 + ⟪u,e⟫) • (u + e)`

is the rotation of `ℝⁿ` in the plane `span {u,e}` carrying `u` to `e` and fixing the orthogonal
complement `(span {u,e})^⊥`.  It is the explicit form of the "parallel transport" of the incidence
fibration `(P,w) ↦ w/‖w‖` of the sphere bundle of the tautological bundle: it is *linear* in `x`
and *continuous* in `u` on the region `⟪u,e⟫ ≠ -1`.

This module only fixes the formula (and the elementary rewriting lemmas used to compute with it);
the geometric properties are in `Submission/Work/ThomBordism/Grassmann/Rotation.lean`.
-/

open scoped RealInnerProductSpace

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {n : ℕ}

/-- The rotation carrying the unit vector `u` to the unit vector `e` inside the plane spanned by
them. -/
def rotMap (u e x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x + (inner ℝ x u) • (e - u) -
    ((inner ℝ x e - (inner ℝ x u) * (inner ℝ u e)) / (1 + inner ℝ u e)) • (u + e)

@[simp] theorem rotMap_zero (u e : EuclideanSpace ℝ (Fin n)) : rotMap u e 0 = 0 := by
  simp [rotMap]

theorem rotMap_linear (u e : EuclideanSpace ℝ (Fin n)) (a b : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    rotMap u e (a • x + b • y) = a • rotMap u e x + b • rotMap u e y := by
  simp only [rotMap, inner_add_left, inner_smul_left, add_smul, smul_add, add_mul,
    starRingEnd_apply, star_trivial]
  module

end

end Work.ThomBordism.Grassmann
