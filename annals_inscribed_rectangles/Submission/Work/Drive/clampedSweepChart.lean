import Mathlib
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.fderiv_const_along

/-!
# The radial sweep in the coordinates `(0,∞) × ℝP³`

`Work.Drive.clampedSweep c ψ P x = scaleCapping (clampScale c ψ P x) (P (x 0, x 1))`
(`Submission/Work/Drive/clampedSweep.lean`) is the chain whose `x 2 = 1` face is the plane `P` and
whose `x 2 = 0` face is the shadow of `P` on the level `c`.

This file records its shape in the transparent coordinates of the capping space: the *projective
class* of the sweep at a parameter `x` is that of the plane at `(x 0, x 1)` — **independent of
`x 2`** — while the radial coordinate is the plane's radial coordinate scaled by the interpolation
factor `clampScale`.  In other words the sweep moves along the radial direction of a fixed projective
class, which is what makes its derivative a radial line plus the class-derivative of the plane, and
is the structural input of the genericity computation of `CONCRETE_CHAINS_STATUS.md` §3.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

/-- **The projective class of the radial sweep is that of its plane**, and in particular does not
depend on the sweep parameter `x 2`. -/
theorem cappingSpaceHomeoProj_clampedSweep_snd
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).2
      = (Work.Drive.cappingSpaceHomeoProj (P (mk2 (x 0) (x 1)))).2 := by
  rw [clampedSweep_apply, CapSmooth.cappingSpaceHomeoProj_scaleCapping]

/-- **The radial coordinate of the sweep** is the plane's radial coordinate scaled by `clampScale`. -/
theorem levelOf_clampedSweep
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (x : EuclideanSpace ℝ (Fin 3)) :
    levelOf (clampedSweep c ψ P x)
      = clampScale c ψ P x * levelOf (P (mk2 (x 0) (x 1))) := by
  rw [clampedSweep_apply, levelOf, CapSmooth.cappingSpaceHomeoProj_scaleCapping]
  rfl

open scoped Manifold ContDiff

open Manifold in
/-- **The logarithm of the radial coordinate of the sweep**, explicitly: the plane's radial coordinate
`r` is scaled by `exp (ψ (x 2) · (log c - log r))`. -/
theorem log_levelOf_clampedSweep
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (x : EuclideanSpace ℝ (Fin 3)) :
    Real.log (levelOf (clampedSweep c ψ P x))
      = ψ (x 2) * (Real.log c - Real.log (levelOf (P (mk2 (x 0) (x 1)))))
        + Real.log (levelOf (P (mk2 (x 0) (x 1)))) := by
  have hr : 0 < levelOf (P (mk2 (x 0) (x 1))) := levelOf_pos _
  have hA : 0 < clampScale c ψ P x := clampScale_pos c ψ P x
  rw [levelOf_clampedSweep, clampScale, Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hr),
    Real.log_exp]

/-- The class component of the sweep is the class component of the plane read through the projection
`x ↦ (x 0, x 1)` of the parameter cube. -/
theorem cappingSpaceHomeoProj_clampedSweep_snd_eq
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace) :
    (fun x : EuclideanSpace ℝ (Fin 3) =>
        (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).2)
      = fun x : EuclideanSpace ℝ (Fin 3) =>
          (Work.Drive.cappingSpaceHomeoProj (P (mk2 (x 0) (x 1)))).2 :=
  funext fun x => cappingSpaceHomeoProj_clampedSweep_snd c ψ P x

section ClassDerivative

/-! ## The class component does not move along the sweep direction

Since the projective class of `clampedSweep c ψ P x` is that of the plane at `(x 0, x 1)`
(`cappingSpaceHomeoProj_clampedSweep_snd`), the class component is constant along the affine lines
`t ↦ x + t • e₂`, so `Work.Drive.fderiv_apply_eq_zero_of_const_along` kills the `e₂` direction.  This is
the statement in the chart coordinates of `ℝP³` (`projChartMap ind`), which is the form in which the
genericity of the concrete chains is checked. -/

/-- **The `x 2`-derivative of the projective class of a radial sweep vanishes.** -/
theorem fderiv_projChartMap_snd_clampedSweep_apply_single
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (ind : Fin 4) (x : EuclideanSpace ℝ (Fin 3))
    (hF : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.Drive.projChartMap ind
        ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).2)) x) :
    fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.Drive.projChartMap ind
          ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).2)) x
        (EuclideanSpace.single 2 (1 : ℝ)) = 0 := by
  refine fderiv_apply_single_two_eq_zero_of_dependsOn _ x hF ?_
  intro u v hu0 hu1
  rw [cappingSpaceHomeoProj_clampedSweep_snd, cappingSpaceHomeoProj_clampedSweep_snd,
    show mk2 (u 0) (u 1) = mk2 (v 0) (v 1) by rw [hu0, hu1]]

end ClassDerivative

end

end Work.Drive
