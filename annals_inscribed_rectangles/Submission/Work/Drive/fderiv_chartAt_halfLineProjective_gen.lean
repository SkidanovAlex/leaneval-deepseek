import Mathlib
import Submission.Work.Drive.fderiv_chartAt_halfLineProjective

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

theorem fderiv_chartAt_halfLineProjective_gen {k : ℕ}
    (G : EuclideanSpace ℝ (Fin k) → Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (x : EuclideanSpace ℝ (Fin k))
    (p : Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (h₁ : DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
            (Homeomorph.chartedSpace Work.Drive.expHomeo) p.1 (G u).1) x)
    (h₂ : DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
            (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
            (Work.Drive.projCharted 3) p.2 (G u).2) x) :
    fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _ _ _
        Work.Drive.halfLineProjectiveCharted p (G u)) x
      = (Work.Drive.psiEquiv : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
            EuclideanSpace ℝ (Fin 4)).comp
        ((fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
              (Homeomorph.chartedSpace Work.Drive.expHomeo) p.1 (G u).1) x).prod
          (fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
              (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
              (Work.Drive.projCharted 3) p.2 (G u).2) x)) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ)) :=
    Homeomorph.chartedSpace Work.Drive.expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ))
      (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
  have hchart : (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _ _ _
        Work.Drive.halfLineProjectiveCharted p (G u))
      = fun u => (Work.Drive.psiEquiv : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
            EuclideanSpace ℝ (Fin 4))
          (chartAt (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) p (G u)) := by
    funext u
    rfl
  rw [hchart]
  have hfun : (fun u => (Work.Drive.psiEquiv :
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) →L[ℝ] EuclideanSpace ℝ (Fin 4))
          (chartAt (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) p (G u)))
      = ⇑Work.Drive.psiEquiv ∘ fun u => (chartAt (EuclideanSpace ℝ (Fin 1)) p.1 (G u).1,
            chartAt (EuclideanSpace ℝ (Fin 3)) p.2 (G u).2) := by
    funext u
    rw [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_apply]
    rfl
  rw [hfun, ContinuousLinearEquiv.comp_fderiv]
  congr 1
  exact DifferentiableAt.fderiv_prodMk h₁ h₂

end

end Work.Drive
