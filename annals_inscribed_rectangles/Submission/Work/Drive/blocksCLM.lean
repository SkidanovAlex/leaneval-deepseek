import Mathlib
import Submission.Work.Drive.mk2CLM
import Submission.Work.Drive.clampedSweepChart
import Submission.Work.Drive.fderiv_log_levelOf_clampedSweep_apply
import Submission.Work.Drive.fderiv_projChartMap_snd_clampedSweep_apply

/-!
# The two blocks of the derivative of a radial sweep, as continuous linear maps

`Work.Drive.fderiv_log_levelOf_clampedSweep_apply` and
`Work.Drive.fderiv_projChartMap_snd_clampedSweep_apply` give the two components of the derivative of a
radial sweep evaluated on an arbitrary vector.  This file rewrites them in the *block form* used by
`Work.Drive.tripleTransverseE_of_blocks`: with `π := Work.Drive.mk2CLM` (the plane's parameter) and
`τ := Work.Drive.coordCLM2` (the radial parameter),

* the level block has the shape `b ∘ π + a • τ`,
* the class block has the shape `c ∘ π` (in particular it does not involve the radial parameter).
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

/-- **The level block, in block form.** -/
theorem fderiv_log_levelOf_clampedSweep_eq
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (x : EuclideanSpace ℝ (Fin 3))
    (hlog : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) Work.Drive.Ctop
      (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y)))
      (Work.Drive.mk2 (x 0) (x 1))) :
    fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
        Real.log (Work.Drive.levelOf (Work.Drive.clampedSweep c ψ P u))) x
      = (1 - ψ (x 2)) • ((fderiv ℝ
            (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y)))
            (Work.Drive.mk2 (x 0) (x 1))).comp mk2CLM)
        + (deriv ψ (x 2) * (Real.log c
            - Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0) (x 1)))))) • coordCLM2 := by
  apply ContinuousLinearMap.ext
  intro w
  rw [fderiv_log_levelOf_clampedSweep_apply c ψ P hψ x w hlog]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, mk2CLM_apply, coordCLM2_apply, smul_eq_mul]
  ring

/-- **The class block, in block form**: it is `c ∘ π`, with no radial component. -/
theorem fderiv_projChartMap_snd_clampedSweep_eq
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (ind : Fin 4) (x : EuclideanSpace ℝ (Fin 3))
    (hF : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
      Work.Drive.projChartMap ind ((Work.Drive.cappingSpaceHomeoProj (P y)).2))
      (Work.Drive.mk2 (x 0) (x 1))) :
    fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.Drive.projChartMap ind
          ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep c ψ P u)).2)) x
      = (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap ind ((Work.Drive.cappingSpaceHomeoProj (P y)).2))
          (Work.Drive.mk2 (x 0) (x 1))).comp mk2CLM := by
  apply ContinuousLinearMap.ext
  intro w
  rw [fderiv_projChartMap_snd_clampedSweep_apply c ψ P ind x w hF]
  simp [ContinuousLinearMap.comp_apply]

end

end Work.Drive
