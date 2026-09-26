import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

namespace Work.Topology.SphereSlicing

open Submission

/-- The box norm is homogeneous: scaling about the centre `c` by `t` scales the norm by `|t|`.

Since `EuclideanSpace ℝ (Fin 3)` is a product, the `i`-th coordinate of `c + t • (y - c)` is
`c i + t * (y i - c i)`, so `|(c + t • (y - c)) i - c i| = |t| * |y i - c i|`; dividing by the
positive side length `boxSide i` and pulling the common factor `|t|` out of the maximum of the
three coordinates gives the claim. -/
theorem boxNorm_homogeneous (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (t : ℝ) (y : LeanEval.KnotTheory.PardonDistortion.R3) :
    Submission.boxNorm c σ (c + t • (y - c)) = |t| * Submission.boxNorm c σ y := by
  have h : ∀ i : Fin 3, |(c + t • (y - c)) (σ i) - c (σ i)| / boxSide i
      = |t| * (|y (σ i) - c (σ i)| / boxSide i) := by
    intro i
    rw [show (c + t • (y - c)) (σ i) - c (σ i) = t * (y (σ i) - c (σ i)) by simp]
    rw [abs_mul]
    ring
  rw [Submission.boxNorm, Submission.boxNorm, h 0, h 1, h 2]
  simp only [mul_max_of_nonneg _ _ (abs_nonneg t)]

end Work.Topology.SphereSlicing
