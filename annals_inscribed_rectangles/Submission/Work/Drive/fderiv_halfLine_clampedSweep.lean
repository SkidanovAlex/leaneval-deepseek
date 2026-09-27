import Mathlib
import Submission.Work.Drive.fderiv_chartAt_halfLineProjective
import Submission.Work.Drive.fderiv_chartAt_expHomeo
import Submission.Work.Drive.blocksCLM

/-!
# The chart derivative of a radial sweep, as the pair of its two blocks

`Work.Drive.fderiv_chartAt_halfLineProjective` gives the derivative of the chart of the capping model
along a curve as `psiEquiv ∘ (chart₁-component × chart₂-component)`.  This file evaluates the two
components for a **radial sweep** `clampedSweep c ψ P` (`Submission/Work/Drive/clampedSweep.lean`):

* the first component is `logEucl ∘ (the level block)`, with
  `Work.Drive.fderiv_chartAt_expHomeo` for the chart of `(0,∞)`;
* the second is the plane's *class block* (the chart of `ℝP³` is `projChartMap ind`).

This is the last identification needed to feed the block-level genericity criterion
`Work.Drive.tripleTransverseE_clampedSweeps` into the manifold-level transversality of the engine
(`Work.Drive.Meet3Generic.trans`).
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

/-- **The chart of `ℝP³` is a concrete projective chart.** -/
theorem fderiv_chartAt_projCharted
    {n : ℕ} (i : Fin (n + 1))
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (G : Z → Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (z : Z)
    (hchart : (@chartAt (EuclideanSpace ℝ (Fin n)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1)))) _
        (Work.Drive.projCharted n) (G z) :
        OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1))))
          (EuclideanSpace ℝ (Fin n)))
      = Work.Drive.projChart i) :
    fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin n)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1)))) _ (Work.Drive.projCharted n)
        (G z) (G u)) z
      = fderiv ℝ (fun u => Work.Drive.projChartMap i (G u)) z := by
  simp only [hchart, Work.Drive.projChart_apply]

/-- **The chart derivative of a radial sweep, in block form.** -/
theorem fderiv_chartAt_halfLine_clampedSweep
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (ind : Fin 4)
    (x : EuclideanSpace ℝ (Fin 3))
    (hchart2 : (@chartAt (EuclideanSpace ℝ (Fin 3)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
        (Work.Drive.projCharted 3)
        (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).2 :
        OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
          (EuclideanSpace ℝ (Fin 3)))
      = Work.Drive.projChart ind)
    (hrc : ContinuousAt (fun u => (Work.Drive.cappingSpaceHomeoProj
      (clampedSweep c ψ P u)).1) x)
    (hrd : DifferentiableAt ℝ (fun u => Real.log
      ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).1 : ℝ)) x)
    (hz : (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).1 ∈
        (@chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
          (Homeomorph.chartedSpace Work.Drive.expHomeo)
          (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).1).source)
    (h₁ : DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
          (Homeomorph.chartedSpace Work.Drive.expHomeo)
          (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).1
          ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).1)) x)
    (h₂ : DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
          (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3)
          (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).2
          ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).2)) x) :
    fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
        (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
        Work.Drive.halfLineProjectiveCharted
        (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x))
        (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u))) x
      = (Work.Drive.psiEquiv : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
            EuclideanSpace ℝ (Fin 4)).comp
        ((Work.Drive.logEucl.comp (fderiv ℝ (fun u => Real.log
              (Work.Drive.levelOf (clampedSweep c ψ P u))) x)).prod
          (fderiv ℝ (fun u => Work.Drive.projChartMap ind
              ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).2)) x)) := by
  have hA : fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
      (Homeomorph.chartedSpace Work.Drive.expHomeo)
      (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).1
      ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).1)) x
      = Work.Drive.logEucl.comp (fderiv ℝ (fun u => Real.log
          ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).1 : ℝ)) x) :=
    fderiv_chartAt_expHomeo (fun u => (Work.Drive.cappingSpaceHomeoProj
      (clampedSweep c ψ P u)).1) x
      (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).1 hrc hz hrd
  have hB : fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3)
      (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).2
      ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).2)) x
      = fderiv ℝ (fun u => Work.Drive.projChartMap ind
          ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).2)) x :=
    fderiv_chartAt_projCharted ind
      (fun u => (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).2) x hchart2
  rw [fderiv_chartAt_halfLineProjective
    (G := fun u => Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)) x
    (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)) h₁ h₂, hA, hB]
  simp only [Work.Drive.levelOf]

/-- The same with a freely given chart point. -/
theorem fderiv_chartAt_halfLine_clampedSweep_chartAt
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (ind : Fin 4)
    (q : Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (x : EuclideanSpace ℝ (Fin 3))
    (hq1 : (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).1 = q.1)
    (hq2 : (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).2 = q.2)
    (hchart2 : (@chartAt (EuclideanSpace ℝ (Fin 3)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
        (Work.Drive.projCharted 3) q.2 :
        OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
          (EuclideanSpace ℝ (Fin 3)))
      = Work.Drive.projChart ind)
    (hrc : ContinuousAt (fun u => (Work.Drive.cappingSpaceHomeoProj
      (clampedSweep c ψ P u)).1) x)
    (hrd : DifferentiableAt ℝ (fun u => Real.log
      ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).1 : ℝ)) x)
    (hz : (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)).1 ∈
        (@chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
          (Homeomorph.chartedSpace Work.Drive.expHomeo) q.1).source)
    (h₁ : DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
          (Homeomorph.chartedSpace Work.Drive.expHomeo) q.1
          ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).1)) x)
    (h₂ : DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
          (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3) q.2
          ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).2)) x) :
    fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
        (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
        Work.Drive.halfLineProjectiveCharted q
        (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u))) x
      = (Work.Drive.psiEquiv : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
            EuclideanSpace ℝ (Fin 4)).comp
        ((Work.Drive.logEucl.comp (fderiv ℝ (fun u => Real.log
              (Work.Drive.levelOf (clampedSweep c ψ P u))) x)).prod
          (fderiv ℝ (fun u => Work.Drive.projChartMap ind
              ((Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P u)).2)) x)) := by
  have hq : (Work.Drive.cappingSpaceHomeoProj (clampedSweep c ψ P x)) = q := Prod.ext hq1 hq2
  rw [← hq] at hchart2 hz h₁ h₂ ⊢
  exact fderiv_chartAt_halfLine_clampedSweep c ψ P ind x hchart2 hrc hrd hz h₁ h₂

end

end Work.Drive
