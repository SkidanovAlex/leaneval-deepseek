import Mathlib
import Submission.Work.Drive.mk2CLM
import Submission.Work.Drive.mk2CLM_coordinate_split
import Submission.Work.Drive.blocksCLM
import Submission.Work.Drive.tripleTransverseE_of_blocks

/-!
# The transversality of three radial sweeps, reduced to the geometric data of their planes

This file assembles the genericity computation of the counting chapter
(`Submission/Work/Drive/GENERICITY_INTERFACE_STATUS.md`) into one statement: for three radial sweeps
`Work.Drive.clampedSweep (c k) ψ (P k)` (`k = 0,1,2`), the transversality of their derivatives at a
triple point follows from the two *blocks* of each derivative:

* the **radial condition** — the coefficient
  `a k = deriv ψ (x k 2) * (log (c k) - log (levelOf (P k (x k 0, x k 1))))` is non-zero, i.e. the
  sweep really moves in the radial direction; and
* the **general position of the three planes** — the class-derivatives
  `c k = fderiv (projChartMap (ind k) ∘ cls ∘ P k) (x k 0, x k 1)` are injective with
  `(c 0).range ⊓ (c 1).range ⊓ (c 2).range = ⊥`, i.e. the three `2`-planes `im c k ⊆ T ℝP³` span.

The proof is the composition of `Work.Drive.fderiv_log_levelOf_clampedSweep_eq` and
`Work.Drive.fderiv_projChartMap_snd_clampedSweep_eq` (the block forms) with
`Work.Drive.tripleTransverseE_of_blocks` (the criterion) and
`Work.Drive.mk2CLM_coordinate_split` (the two witnesses for `π` and `τ`).
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

/-- **The transversality of three radial sweeps from the data of their planes.** -/
theorem tripleTransverseE_clampedSweeps
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (ind : Fin 3 → Fin 4)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hlog : ∀ k, ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) Work.Drive.Ctop
        (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P k y)))
        (Work.Drive.mk2 (x k 0) (x k 1)))
    (hF : ∀ k, DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
        (Work.Drive.mk2 (x k 0) (x k 1)))
    (ha : ∀ k, deriv ψ (x k 2) * (Real.log (c k)
        - Real.log (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1))))) ≠ 0)
    (hc : ∀ k, Function.Injective (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
        (Work.Drive.mk2 (x k 0) (x k 1))))
    (hV : (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind 0) ((Work.Drive.cappingSpaceHomeoProj (P 0 y)).2))
          (Work.Drive.mk2 (x 0 0) (x 0 1))).range ⊓
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind 1) ((Work.Drive.cappingSpaceHomeoProj (P 1 y)).2))
          (Work.Drive.mk2 (x 1 0) (x 1 1))).range ⊓
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind 2) ((Work.Drive.cappingSpaceHomeoProj (P 2 y)).2))
          (Work.Drive.mk2 (x 2 0) (x 2 1))).range = ⊥) :
    Work.Drive.TripleTransverseE
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
          Real.log (Work.Drive.levelOf (Work.Drive.clampedSweep (c 0) ψ (P 0) u))) (x 0)).prod
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.Drive.projChartMap (ind 0) ((Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c 0) ψ (P 0) u)).2)) (x 0)))
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
          Real.log (Work.Drive.levelOf (Work.Drive.clampedSweep (c 1) ψ (P 1) u))) (x 1)).prod
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.Drive.projChartMap (ind 1) ((Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c 1) ψ (P 1) u)).2)) (x 1)))
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
          Real.log (Work.Drive.levelOf (Work.Drive.clampedSweep (c 2) ψ (P 2) u))) (x 2)).prod
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.Drive.projChartMap (ind 2) ((Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c 2) ψ (P 2) u)).2)) (x 2))) := by
  have h0 := fderiv_log_levelOf_clampedSweep_eq (c 0) ψ (P 0) hψ (x 0) (hlog 0)
  have h1 := fderiv_log_levelOf_clampedSweep_eq (c 1) ψ (P 1) hψ (x 1) (hlog 1)
  have h2 := fderiv_log_levelOf_clampedSweep_eq (c 2) ψ (P 2) hψ (x 2) (hlog 2)
  have g0 := fderiv_projChartMap_snd_clampedSweep_eq (c 0) ψ (P 0) (ind 0) (x 0) (hF 0)
  have g1 := fderiv_projChartMap_snd_clampedSweep_eq (c 1) ψ (P 1) (ind 1) (x 1) (hF 1)
  have g2 := fderiv_projChartMap_snd_clampedSweep_eq (c 2) ψ (P 2) (ind 2) (x 2) (hF 2)
  rw [h0, h1, h2, g0, g1, g2]
  exact tripleTransverseE_of_blocks mk2CLM coordCLM2
    mk2CLM_coordinate_split.1 mk2CLM_coordinate_split.2
    (fun k => deriv ψ (x k 2) * (Real.log (c k)
      - Real.log (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1)))))) ha
    (fun k => (1 - ψ (x k 2)) • (fderiv ℝ
      (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P k y)))
      (Work.Drive.mk2 (x k 0) (x k 1))))
    (fun k => fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
      Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
      (Work.Drive.mk2 (x k 0) (x k 1)))
    hc hV

end

end Work.Drive
