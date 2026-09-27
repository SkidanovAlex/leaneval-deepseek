import Mathlib
import Submission.Work.Drive.squareSystemForm

/-!
# Smoothness of the class-difference form `qform`

`Work.Drive.qform` is the bilinear form on `Work.Drive.Eucl 3 = ℝ⁴ ≅ ℍ` whose vanishing is the
*class equality* on `ℝP³`; see `Submission/Work/Drive/squareSystemForm.lean`.  Here we record that it
is a `C^∞` function of the pair `(v, w)`, i.e. that the associated map on `Eucl 3 × Eucl 3` is smooth.
This is what lets the system built from it be treated as a smooth map of the parameters.

The proof is coordinatewise: `contDiff_piLp` reduces the target `EuclideanSpace ℝ (Fin 3)` to its
`Fin 3` coordinates, at which point the formula is a polynomial in the coordinates of `v` and `w`
(the cross product is expanded with `cross_apply`), so `fun_prop` closes it.
-/

namespace Work.Drive

open scoped ContDiff Topology

theorem contDiff_qform :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Work.Drive.Eucl 3 × Work.Drive.Eucl 3 => Work.Drive.qform p.1 p.2) := by
  -- reduce the `Fin 3`-valued target to its coordinates
  rw [contDiff_piLp (p := 2)]
  intro k
  -- expose the (polynomial) coordinate formula
  simp only [qform, WithLp.ofLp_toLp, cross_apply]
  -- the three coordinates are the same polynomial shape
  fin_cases k <;> simp [imagPart_ofLp] <;> fun_prop

end Work.Drive
