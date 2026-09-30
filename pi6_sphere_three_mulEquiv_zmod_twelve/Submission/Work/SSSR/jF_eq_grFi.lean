import Mathlib
import Submission.Work.SSSR.serreE1CruxDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The map `Work.SSSR.jF` of the exact couple, in degree `s`, is the map on homology induced by the
projection `grFι R` onto the `s`-th graded piece.

Route: `cases s`; for `s = 0` both sides are `𝟙` (`Work.SSSR.grFι_zero`,
`HomologicalComplex.homologyMap_id`), for `s = k+1` both sides are
`homologyMap (cokernel.π (incF ...))` definitionally. -/
theorem jF_eq_grFi (p : C(E, B)) (s t : ℕ) :
    Work.SSSR.jF (Work.SSSR.xiCan p) s t
      = HomologicalComplex.homologyMap (Work.SSSR.grFι R (Work.SSSR.sSingP p) s) (s + t) := by
  cases s with
  | zero =>
    rw [Work.SSSR.jF, Work.SSSR.grFι_zero]
    exact (HomologicalComplex.homologyMap_id
      ((Work.SSSR.serF R (Work.SSSR.sSingP p)).obj 0) (0 + t)).symm
  | succ k => rfl

end Work.SSSR
