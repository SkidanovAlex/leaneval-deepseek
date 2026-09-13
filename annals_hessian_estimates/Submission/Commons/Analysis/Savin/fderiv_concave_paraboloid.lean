import Mathlib.Analysis.InnerProductSpace.Calculus

/-
# First derivative of Savin's concave paraboloid

Savin, *Small perturbation solutions for elliptic equations*, CPDE 32 (2007) 557--578.

The concave paraboloid of opening `a`, vertex `y` and vertical offset `c` is
`z ↦ -(a/2)‖z - y‖² + c`.  This file computes its first derivative:
`D(-(a/2)‖· - y‖² + c)(x) = -(a • innerSL ℝ (x - y))`.

The Hessian of this paraboloid (`-(a • 1)`) is the object slid from below in
Savin's sliding-paraboloid argument; see `hessian_concave_paraboloid`.
-/

namespace Commons.Analysis.Savin

open scoped RealInnerProductSpace in
theorem fderiv_concave_paraboloid (a c : ℝ) (y : EuclideanSpace ℝ (Fin 4))
    (x : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) => -(a / 2) * ‖z - y‖ ^ 2 + c) x
      = -(a • (innerSL ℝ (x - y))) := by
  -- First derivative of `z ↦ ‖z - y‖²` at `x` is `2 • innerSL ℝ (x - y)`.
  have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 4) => ‖z - y‖ ^ 2)
      (2 • (innerSL ℝ (x - y))) x := by
    have hsub : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 4) => z - y)
        (1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) x :=
      (hasFDerivAt_id x).sub_const y
    have hcomp := (hasStrictFDerivAt_norm_sq (x - y)).hasFDerivAt.comp x hsub
    have heq : ((2 : ℕ) • (innerSL ℝ (x - y)))
          ∘SL (1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
        = (2 : ℕ) • (innerSL ℝ (x - y)) := by
      rw [show (1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
          = ContinuousLinearMap.id ℝ _ from rfl, ContinuousLinearMap.comp_id]
    rw [heq] at hcomp
    exact hcomp
  -- Scale by `-(a/2)` and add the constant `c` (whose derivative vanishes).
  have h := (h1.const_mul (-(a / 2))).add_const c
  rw [h.fderiv]
  ext v
  simp only [smul_apply, neg_apply]
  simp
  ring

end Commons.Analysis.Savin