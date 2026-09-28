import Mathlib
import Submission.Work.SSS.serreE1CruxDefs

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The map `Work.SSS.jF` of the exact couple, in degree `s`, is the map on homology induced by the
projection `grFι` onto the `s`-th graded piece.

Route: `cases s`; for `s = 0` both sides are `𝟙` (`Work.SSS.grFι_zero`,
`HomologicalComplex.homologyMap_id`), for `s = k+1` both sides are
`homologyMap (cokernel.π (incF ...))` definitionally. -/
theorem jF_eq_grFi (p : C(E, B)) (s t : ℕ) :
    Work.SSS.jF (Work.SSS.xiCan p) s t
      = HomologicalComplex.homologyMap (Work.SSS.grFι (Work.SSS.sSingP p) s) (s + t) := by
  cases s with
  | zero =>
    rw [Work.SSS.jF, Work.SSS.grFι_zero]
    exact (HomologicalComplex.homologyMap_id
      ((Work.SSS.serF (Work.SSS.sSingP p)).obj 0) (0 + t)).symm
  | succ k => rfl

end Work.SSS
