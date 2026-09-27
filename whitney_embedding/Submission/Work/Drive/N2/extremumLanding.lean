import Mathlib
import Submission.Work.Drive.N2.exists_extremumModelRegion

/-!
# The extremum's landing row, exported

`Work.Drive.N2.journey_avoids_modelBalls` (PROVED) says that the trajectory of a band point of an
extremum window, starting *off* the model ball `modelBall (φ j) (ρ j / 8)`, avoids *all* the model
balls of the datum up to the anchor level.  Together with the datum's law `WindowDatum.hlevel`
(the level law off the balls) this is the **landing row** of the window's transport:

    f (Φ (f p + s η - f x, x)) = f p + s η.

The row is exported here in the form the assembly consumes: it is *not* tied to a particular window
width (any `η ≤ D.ηd` and any `x` of the band will do), so it serves both the window band and the
neighbouring value bands.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

open scoped Manifold ContDiff in
/-- **The extremum landing row.** -/
theorem extremumLanding {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hext : D.s₁ D.j = D.s₂ D.j)
    {η : ℝ} (hη : 0 < η) (hηd : η ≤ D.ηd) {x : M}
    (hx : x ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j / 8))
    (hband : f x ∈ Set.Ioo (f p - η) (f p + η)) :
    f (D.Φ (f p + D.s₁ D.j * η - f x, x)) = f p + D.s₁ D.j * η := by
  classical
  set t : ℝ := f p + D.s₁ D.j * η - f x with htdef
  have havoid := Work.Drive.N2.journey_avoids_modelBalls D hext hη hηd hx hband
  have hlevel := D.hlevel x t (fun u hu => havoid u hu)
  rw [hlevel]
  ring

end Work.Drive.N2
