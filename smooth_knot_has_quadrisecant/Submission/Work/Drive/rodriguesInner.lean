import Mathlib
import Submission.Work.Drive.framePathDefs

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# The Rodrigues rotation preserves the inner product

`rodrigues n α x = cos α • x + sin α • (n × x) + (1 - cos α) * ⟪n, x⟫ • n` is the
rotation of `x` about the (unit) axis `n` through the angle `α`.  Here we prove
that it is an isometry of the Euclidean space `Space`:

`⟪rodrigues n α x, rodrigues n α y⟫ = ⟪x, y⟫` whenever `‖n‖ = 1`.

The proof is the direct bilinear expansion, together with the two elementary
identities
* `inner_crossv_swap` : the map `x ↦ n × x` is skew-adjoint,
* `inner_crossv_crossv` : `⟪n × x, n × y⟫ = ⟪x, y⟫ - ⟪n, x⟫ * ⟪n, y⟫` for `‖n‖ = 1`,
and the trigonometric identity `cos ^ 2 + sin ^ 2 = 1`.
-/

/-- The cross product with `n` is skew-adjoint:
`⟪n × x, y⟫ = -⟪x, n × y⟫`. -/
lemma inner_crossv_swap (n x y : Space) :
    inner ℝ (crossv n x) y = - inner ℝ x (crossv n y) := by
  rw [inner_eq_dot, inner_eq_dot, crossv_ofLp, crossv_ofLp, dotProduct_comm]
  rw [triple_product_permutation y n x, triple_product_permutation x n y]
  have h : crossProduct y.ofLp x.ofLp = -(crossProduct x.ofLp y.ofLp) := by
    rw [← cross_anticomm]
  rw [h, dotProduct_neg, neg_neg]

/-- **Binet–Cauchy formula for the cross product of `n` with two vectors**: for a
unit vector `n`, `⟪n × x, n × y⟫ = ⟪x, y⟫ - ⟪n, x⟫ * ⟪n, y⟫`. -/
lemma inner_crossv_crossv {n x y : Space} (hn : ‖n‖ = 1) :
    inner ℝ (crossv n x) (crossv n y) = inner ℝ x y - inner ℝ n x * inner ℝ n y := by
  rw [inner_eq_dot, inner_eq_dot, inner_eq_dot, inner_eq_dot, crossv_ofLp, crossv_ofLp,
    cross_dot_cross]
  have hn2 : n.ofLp ⬝ᵥ n.ofLp = 1 := by
    rw [← inner_eq_dot, real_inner_self_eq_norm_sq, hn, one_pow]
  rw [hn2, one_mul, dotProduct_comm n.ofLp x.ofLp]
  ring

/-- The Rodrigues rotation about a unit axis is an isometry. -/
theorem rodriguesInner {n x y : LeanEval.KnotTheory.Quadrisecant.Space} (hn : ‖n‖ = 1)
    (α : ℝ) :
    inner ℝ (Work.Drive.rodrigues n α x) (Work.Drive.rodrigues n α y) = inner ℝ x y := by
  simp only [rodrigues, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [inner_crossv_crossv hn, inner_crossv_self, inner_self_crossv, inner_crossv_swap,
    real_inner_comm x n]
  have hnn : inner ℝ n n = 1 := by
    rw [real_inner_self_eq_norm_sq, hn, one_pow]
  rw [hnn]
  ring_nf
  rw [Real.sin_sq]
  ring

end Work.Drive
