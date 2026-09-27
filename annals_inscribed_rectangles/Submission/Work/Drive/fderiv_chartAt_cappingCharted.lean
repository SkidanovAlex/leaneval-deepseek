import Mathlib
import Submission.Work.Drive.chartAt_homeomorph_chartedSpace
import Submission.Work.Drive.cappingCharted

/-!
# The derivative of the chart of the capping space

`Work.Drive.cappingCharted` is the transparent smooth structure on the capping space `Y`, obtained by
transporting `Work.Drive.halfLineProjectiveCharted` (a structure on `(0,∞) × ℝP³`) along the concrete
homeomorphism `Work.Drive.cappingSpaceHomeoProj : Y ≃ₜ (0,∞) × ℝP³`.

This file records the consequence for derivatives: the chart of `Y` evaluated along a curve is, up to
reparametrisation by `cappingSpaceHomeoProj`, the chart of `(0,∞) × ℝP³` evaluated along the
transported curve,

> `fderiv (chartAt p ∘ D) x = fderiv (chartAt (cappingSpaceHomeoProj p) ∘ cappingSpaceHomeoProj ∘ D) x`.

With `Work.Drive.fderiv_chartAt_halfLineProjective` this turns every derivative computation in the
capping space into one in the coordinates `(0,∞) × ℝP³` of the model.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

theorem fderiv_chartAt_cappingCharted
    (D : EuclideanSpace ℝ (Fin 3) → Work.Drive.CappingSpace)
    (x : EuclideanSpace ℝ (Fin 3)) (p : Work.Drive.CappingSpace)
    (hD : ContinuousAt D x)
    (hz : D x ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ Work.Drive.CappingSpace _
        Work.Drive.cappingCharted p).source) :
    fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _ Work.Drive.CappingSpace _
        Work.Drive.cappingCharted p (D u)) x
      = fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
          (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
          Work.Drive.halfLineProjectiveCharted (Work.Drive.cappingSpaceHomeoProj p)
          (Work.Drive.cappingSpaceHomeoProj (D u))) x := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.halfLineProjectiveCharted
  have h := fderiv_chartAt_homeomorph_chartedSpace (k := 3)
    (H := EuclideanSpace ℝ (Fin 4))
    (M := Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (M' := Work.Drive.CappingSpace)
    (e := Work.Drive.cappingSpaceHomeoProj.symm) (f := D) (z := x) (p := p) hD hz
  show fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _ Work.Drive.CappingSpace _
      (Homeomorph.chartedSpace Work.Drive.cappingSpaceHomeoProj.symm) p (D u)) x
    = fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
        (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
        Work.Drive.halfLineProjectiveCharted (Work.Drive.cappingSpaceHomeoProj p)
        (Work.Drive.cappingSpaceHomeoProj (D u))) x
  exact h

/-- The chart point of the capping space may be taken at the point of the curve. -/
theorem fderiv_chartAt_cappingCharted_self
    (D : EuclideanSpace ℝ (Fin 3) → Work.Drive.CappingSpace)
    (x : EuclideanSpace ℝ (Fin 3)) (hD : ContinuousAt D x) :
    fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _ Work.Drive.CappingSpace _
        Work.Drive.cappingCharted (D x) (D u)) x
      = fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
          (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
          Work.Drive.halfLineProjectiveCharted (Work.Drive.cappingSpaceHomeoProj (D x))
          (Work.Drive.cappingSpaceHomeoProj (D u))) x :=
  fderiv_chartAt_cappingCharted D x (D x) hD
    (@mem_chart_source (EuclideanSpace ℝ (Fin 4)) Work.Drive.CappingSpace _ _
      Work.Drive.cappingCharted (D x))

end

end Work.Drive
