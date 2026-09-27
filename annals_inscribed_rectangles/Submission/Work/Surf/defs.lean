import Mathlib
import Submission.Work.Drive.Surf.Model

/-!
# Setup for the chord-crossing parity

The unit square of the plane (whose boundary is the domain of the difference map `(s,t) ↦ a s - b t`
of two chords) and the ray preimage of a map, used by the mod-2 degree theorem
`Work.Surf.even_ncard_zeros_add_boundary_ray`.
-/

namespace Work.Surf

open Set

noncomputable section

open Work.Drive

/-- The closed unit square of the plane, with coordinates `x 0`, `x 1`. -/
def sqBox : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 1}

/-- The boundary of the unit square: a coordinate is `0` or `1`. -/
def sqBdry : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | x ∈ sqBox ∧ (x 0 = 0 ∨ x 0 = 1 ∨ x 1 = 0 ∨ x 1 = 1)}

/-- The points of the plane at which `F` takes a value on the open ray `{r • v : 0 < r}`. -/
def rayMeet (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∃ r : ℝ, 0 < r ∧ F x = r • v}

end

end Work.Surf
