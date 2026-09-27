import Mathlib
import Submission.Work.Drive.clampedSweepChart
import Submission.Work.Drive.fderiv_mk2_proj_comp_apply

/-!
# The derivative of the projective class of a radial sweep, in full

`Work.Drive.clampedSweepChart` shows that the projective class of the radial sweep
`Work.Drive.clampedSweep c ψ P` at the parameter `x` is the class of the plane `P` at `(x 0, x 1)`:

> `(cappingSpaceHomeoProj (clampedSweep c ψ P x)).2 = (cappingSpaceHomeoProj (P (x 0, x 1))).2`.

Hence, for any chart coordinate `projChartMap ind` of the projective space, the composite

> `u ↦ projChartMap ind ((cappingSpaceHomeoProj (clampedSweep c ψ P u)).2)`

is the composition of the *plane's* class map `y ↦ projChartMap ind ((cappingSpaceHomeoProj (P y)).2)`
with the linear projection `u ↦ (u 0, u 1)` of the parameter cube, so its derivative is the plane's
class derivative read through that projection.  This is the `(x 0, x 1)`-block of the sweep's class
derivative, i.e. step 1 of `GENERICITY_INTERFACE_STATUS.md` §4: with the vanishing of the `x 2`-block
(`Work.Drive.fderiv_projChartMap_snd_clampedSweep_apply_single`) the whole class derivative of the
sweep is that of the plane.
-/

namespace Work.Drive

noncomputable section

/-- **The derivative of the projective class of a radial sweep is the plane's class derivative**,
evaluated on the projected vector.  The hypothesis is exactly the differentiability of the plane's
class map at `(x 0, x 1)`, which is what makes the chain rule applicable (without it `fderiv` is the
zero map on the left, and the identity is false). -/
theorem fderiv_projChartMap_snd_clampedSweep_apply
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (ind : Fin 4) (x w : EuclideanSpace ℝ (Fin 3))
    (hF : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
      Work.Drive.projChartMap ind ((Work.Drive.cappingSpaceHomeoProj (P y)).2))
      (Work.Drive.mk2 (x 0) (x 1))) :
    fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.Drive.projChartMap ind
          ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep c ψ P u)).2)) x w
      = fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap ind ((Work.Drive.cappingSpaceHomeoProj (P y)).2))
          (Work.Drive.mk2 (x 0) (x 1)) (Work.Drive.mk2 (w 0) (w 1)) := by
  have hfun : (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.Drive.projChartMap ind
          ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep c ψ P u)).2))
      = fun u : EuclideanSpace ℝ (Fin 3) =>
          (fun y : EuclideanSpace ℝ (Fin 2) =>
            Work.Drive.projChartMap ind ((Work.Drive.cappingSpaceHomeoProj (P y)).2))
            (Work.Drive.mk2 (u 0) (u 1)) := by
    funext u
    rw [Work.Drive.cappingSpaceHomeoProj_clampedSweep_snd]
  rw [hfun]
  exact Work.Drive.fderiv_mk2_proj_comp_apply
    (fun y : EuclideanSpace ℝ (Fin 2) =>
      Work.Drive.projChartMap ind ((Work.Drive.cappingSpaceHomeoProj (P y)).2)) x w hF

end

end Work.Drive
