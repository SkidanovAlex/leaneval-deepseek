import Mathlib
import Submission.AnalyticUnknot

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# Tools for rotating the frame: cross product, Rodrigues rotation, angles

This file collects the small auxiliary definitions used to build a path of
orthonormal pairs from a given orthonormal pair `(f1, f2)` of `Space` to the
coordinate pair `(e1, e2)`.  Everything here is elementary and self-contained.

* `crossv u v` is Mathlib's `crossProduct` on `Fin 3 → ℝ`, transported to
  `Space = EuclideanSpace ℝ (Fin 3)` along the `WithLp` equivalence;
* `inner_eq_dot`, `norm_sq_crossv` (Lagrange identity) and `crossv_crossv`
  (vector triple product) are the three identities used below;
* `rodrigues n α x` is the rotation of `x` about the axis `n` by the angle `α`
  (`n` is assumed to be a unit vector when this is a rotation);
* `angleOf p q` is the angle of the unit complex number `p + i q`: it is the
  real number `θ` with `cos θ = p`, `sin θ = q` (given `p ^ 2 + q ^ 2 = 1`).

The key properties (`rodrigues` preserving the inner product, and
`angleOf` having the prescribed cosine and sine) are proved in the companion
files `Submission/Work/Drive/rodriguesInner.lean` and
`Submission/Work/Drive/angleOfCosSin.lean`.
-/

noncomputable section

/-- The cross product of two vectors of `Space`, transported from Mathlib's
`crossProduct` on `Fin 3 → ℝ`. -/
noncomputable def crossv (u v : LeanEval.KnotTheory.Quadrisecant.Space) :
    LeanEval.KnotTheory.Quadrisecant.Space :=
  WithLp.toLp 2 (crossProduct u.ofLp v.ofLp)

@[simp] lemma crossv_ofLp (u v : Space) : (crossv u v).ofLp = crossProduct u.ofLp v.ofLp := by
  simp [crossv]

/-- The inner product of `Space` is the dot product of the coordinate vectors. -/
lemma inner_eq_dot (u v : Space) : inner ℝ u v = u.ofLp ⬝ᵥ v.ofLp := by
  simp only [PiLp.inner_apply, Real.inner_apply, dotProduct, mul_comm]

/-- **Lagrange identity**: `‖u × v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2`. -/
lemma norm_sq_crossv (u v : Space) :
    ‖crossv u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - (inner ℝ u v) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (crossv u v), inner_eq_dot, crossv_ofLp, cross_dot_cross,
    ← inner_eq_dot u u, ← inner_eq_dot v v, dotProduct_comm v.ofLp u.ofLp, ← inner_eq_dot u v,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- **Vector triple product**: `(u × v) × w = ⟪u, w⟫ • v - ⟪v, w⟫ • u`. -/
lemma crossv_crossv (u v w : Space) :
    crossv (crossv u v) w = inner ℝ u w • v - inner ℝ v w • u := by
  apply WithLp.ofLp_injective
  rw [crossv_ofLp, crossv_ofLp, cross_cross_eq_smul_sub_smul, inner_eq_dot, inner_eq_dot]
  ext i
  fin_cases i <;> simp [PiLp.smul_apply, PiLp.sub_apply]

/-- The cross product of two vectors is orthogonal to both. -/
lemma inner_crossv_self (u v : Space) : inner ℝ (crossv u v) u = 0 := by
  rw [inner_eq_dot, crossv_ofLp, dotProduct_comm, dot_self_cross]

lemma inner_self_crossv (u v : Space) : inner ℝ u (crossv u v) = 0 := by
  rw [inner_eq_dot, crossv_ofLp]
  exact dot_self_cross u.ofLp v.ofLp


/-- Coordinate form of the cross product on `Space`. -/
lemma crossv_eq_vec (u v : Space) :
    crossv u v = !₂[u.ofLp 1 * v.ofLp 2 - u.ofLp 2 * v.ofLp 1,
      u.ofLp 2 * v.ofLp 0 - u.ofLp 0 * v.ofLp 2,
      u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0] := by
  apply WithLp.ofLp_injective
  simp [crossv, cross_apply]

@[simp] lemma crossv_self (u : Space) : crossv u u = 0 := by
  apply WithLp.ofLp_injective
  rw [crossv_ofLp, cross_self]
  simp

lemma crossv_anticomm (u v : Space) : crossv v u = -crossv u v := by
  apply WithLp.ofLp_injective
  simp only [crossv_ofLp, WithLp.ofLp_neg, cross_anticomm]

lemma crossv_smul_left (a : ℝ) (u v : Space) : crossv (a • u) v = a • crossv u v := by
  apply WithLp.ofLp_injective
  simp only [crossv_ofLp, WithLp.ofLp_smul, map_smul, LinearMap.smul_apply]

lemma crossv_smul_right (a : ℝ) (u v : Space) : crossv u (a • v) = a • crossv u v := by
  apply WithLp.ofLp_injective
  simp only [crossv_ofLp, WithLp.ofLp_smul, map_smul, LinearMap.smul_apply]

lemma crossv_neg_left (u v : Space) : crossv (-u) v = -crossv u v := by
  rw [show (-u : Space) = (-1 : ℝ) • u by simp, crossv_smul_left]
  simp

lemma crossv_neg_right (u v : Space) : crossv u (-v) = -crossv u v := by
  rw [show (-v : Space) = (-1 : ℝ) • v by simp, crossv_smul_right]
  simp

/-- **The Rodrigues rotation**: rotation of `x` about the axis `n` (a unit vector)
by the angle `α`, written in the classical form
`cos α • x + sin α • (n × x) + (1 - cos α) * ⟪n, x⟫ • n`. -/
noncomputable def rodrigues (n : Space) (α : ℝ) (x : Space) : Space :=
  Real.cos α • x + Real.sin α • crossv n x + ((1 - Real.cos α) * inner ℝ n x) • n

/-- The angle of a point of the unit circle: for `p ^ 2 + q ^ 2 = 1`, the number
`angleOf p q` satisfies `cos (angleOf p q) = p` and `sin (angleOf p q) = q`. -/
noncomputable def angleOf (p q : ℝ) : ℝ := Complex.arg (⟨p, q⟩ : ℂ)

end

end Work.Drive
