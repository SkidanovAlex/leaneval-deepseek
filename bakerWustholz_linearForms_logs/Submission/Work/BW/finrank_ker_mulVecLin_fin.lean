import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The kernel of the linear map `v ↦ A.mulVec v` associated with a matrix `A` whose rows are
linearly independent has dimension `N - M`.

This is a direct application of the rank-nullity theorem: the rows of `A = Matrix.of a` are
exactly the family `a`, so `a` being linearly independent forces the range of `A.mulVecLin`
to have dimension `M`. -/
theorem finrank_ker_mulVecLin_fin {F : Type*} [Field F] {M N : ℕ} (a : Fin M → Fin N → F)
    (hind : LinearIndependent F a) :
    Module.finrank F (LinearMap.ker ((Matrix.of a).mulVecLin)) = N - M := by
  -- The rows of `Matrix.of a` are exactly the family `a`.
  have hrow : LinearIndependent F (Matrix.of a).row := hind
  -- Hence the range of `mulVecLin` has dimension `M`.
  have hrank : Module.finrank F (LinearMap.range ((Matrix.of a).mulVecLin)) = M := by
    show (Matrix.of a).rank = M
    rw [LinearIndependent.rank_matrix hrow, Fintype.card_fin]
  -- Rank-nullity applied to `mulVecLin`.
  have hrk := LinearMap.finrank_range_add_finrank_ker (f := (Matrix.of a).mulVecLin)
  rw [hrank, Module.finrank_fintype_fun_eq_card F, Fintype.card_fin] at hrk
  omega

end Work.BW
