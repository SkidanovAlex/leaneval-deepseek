import Mathlib
import Submission.Work.Drive.sqDisk_foldBox_existsUnique
import Submission.Work.Drive.linPlaneChart_eq_iff
import Submission.Work.Drive.planeChain

/-!
# The fibres of the disk presentation of a linear plane, on the *box* model

`Work.Drive.diskPlane Q y = Q (sqDisk (foldBox y))` presents the plane `Q` as a map on the closed
square: the square coordinates are folded into `[0,1]` and then sent to the disk by the square-to-disk
map `sqDisk`.

For the linear plane chart `Q = linPlaneChart φ c hc` the fibres of the disk presentation are known
(`Work.Drive.linPlaneChart_eq_iff`): two points of the closed disk give the same plane point exactly
when they are equal or antipodal boundary points.  Combining this with the fact that the square map
`sqDisk ∘ foldBox` is a bijection of the unit square onto the closed disk
(`Work.Drive.sqDisk_foldBox_existsUnique`), and that the preimage of the **open** disk under `sqDisk`
still has norm `< 1`, one obtains the present statement: for `‖z‖ < 1` there is exactly one point `y`
of the unit square with `diskPlane (linPlaneChart φ c hc) y = linPlaneChart φ c hc z`.

The strict inequality `‖z‖ < 1` is what kills the antipodal alternative: the antipode of a point of
the square's image always has norm `1`, so it can never be `z`.  (For `‖z‖ = 1` the statement would be
*false*: the two antipodal boundary preimages of `z` give the same plane point.)
-/

namespace Work.Drive

open Manifold in
open scoped Manifold ContDiff in
theorem existsUnique_fibre_linPlaneChart (φ : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (c : ℝ)
    (hc : 0 < c) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃! y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 ∧
      Work.Drive.diskPlane (Work.Drive.linPlaneChart φ c hc) y
        = Work.Drive.linPlaneChart φ c hc z := by
  -- the square model of `z`: the unique point of the box with `sqDisk (foldBox y) = z`
  obtain ⟨y, ⟨hybox, hyz⟩, hyuniq⟩ := sqDisk_foldBox_existsUnique z (le_of_lt hz)
  refine ⟨y, ⟨hybox, ?_⟩, ?_⟩
  · rw [diskPlane_apply, hyz]
  · intro y' hy'
    -- the plane point of `y'` is the image of the disk point `sqDisk (foldBox y')`
    have hbox' : foldBox y' ∈ Submission.Drive.unitBox 1 := foldBox_mem_unitBox y'
    have hnorm : ‖sqDisk (foldBox y')‖ ≤ 1 := norm_sqDisk_le_one _ hbox'
    have heq : linPlaneChart φ c hc (sqDisk (foldBox y')) = linPlaneChart φ c hc z := by
      have h := hy'.2
      rwa [diskPlane_apply] at h
    -- the fibre relation of the chart leaves only two alternatives, the second impossible
    rcases (linPlaneChart_eq_iff φ c hc hnorm (le_of_lt hz)).mp heq with h | ⟨-, hz1, -⟩
    · exact hyuniq y' ⟨hy'.1, h⟩
    · exact absurd hz1 (ne_of_lt hz)

end Work.Drive
