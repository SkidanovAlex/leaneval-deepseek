import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.InnerProductSpace

open scoped _root_.Manifold _root_.ContDiff
open _root_.VectorField Bundle
open Filter

/-- The Gram determinant is a quadratic form on pairs: under the change of basis
`(u, v) ↦ (a u + b v, c u + d v)` it picks up the factor `(ad - bc)^2`.  (Lagrange identity /
multiplicativity of the Gram determinant.) -/
theorem inner_gram_basis_change {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u v : F) (a b c d : ℝ) :
    ‖a • u + b • v‖^2 * ‖c • u + d • v‖^2
        - (inner ℝ (a • u + b • v) (c • u + d • v))^2
      = (a * d - b * c)^2 * (‖u‖^2 * ‖v‖^2 - (inner ℝ u v)^2) := by
  have hs : inner ℝ (a • u + b • v) (a • u + b • v)
      = a ^ 2 * inner ℝ u u + 2 * a * b * inner ℝ u v + b ^ 2 * inner ℝ v v := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm u v]
    ring
  have ht : inner ℝ (c • u + d • v) (c • u + d • v)
      = c ^ 2 * inner ℝ u u + 2 * c * d * inner ℝ u v + d ^ 2 * inner ℝ v v := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm u v]
    ring
  have hm : inner ℝ (a • u + b • v) (c • u + d • v)
      = a * c * inner ℝ u u + (a * d + b * c) * inner ℝ u v + b * d * inner ℝ v v := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm u v]
    ring
  rw [← real_inner_self_eq_norm_sq (a • u + b • v),
      ← real_inner_self_eq_norm_sq (c • u + d • v),
      ← real_inner_self_eq_norm_sq u, ← real_inner_self_eq_norm_sq v,
      hs, ht, hm]
  ring

end Commons.Analysis.InnerProductSpace
