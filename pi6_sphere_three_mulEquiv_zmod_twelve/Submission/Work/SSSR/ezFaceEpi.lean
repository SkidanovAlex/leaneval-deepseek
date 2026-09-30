import Mathlib
import Submission.Work.SSSR.serreE1Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite in
/-- If `v : ⦋n⦌ ⟶ ⦋d⦌` is an epimorphism of simplex categories, then for a nondegenerate
`d`-simplex `y` of a simplicial set `Y`, the (possibly degenerate) `n`-simplex `Y.map v.op y`
has the same underlying nondegenerate simplex `N.mk y hy` as `y`: face maps along epis do not
change the nondegenerate simplex a simplex generates. -/
theorem ezFaceEpi {Y : SSet.{0}} {d n : ℕ} (y : Y _⦋d⦌) (hy : y ∈ Y.nonDegenerate d)
    (v : ⦋n⦌ ⟶ ⦋d⦌) (hv : Epi v) :
    (SSet.S.mk (Y.map v.op y)).toN = SSet.N.mk y hy := by
  rw [SSet.S.toN_eq_iff]
  exact (SSet.S.subcomplex_eq_of_epi (SSet.S.mk (Y.map v.op y)) (SSet.S.mk y) v rfl).symm

end Work.SSSR
