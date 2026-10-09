import Mathlib
import Submission.Work.SSGRoute.PT.freeCoverCompat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1cGeneric

theorem freeCoverCompat_single {G H : Type} [Group G] [Group H] (φ : H →* G)
    (X : Rep.{0} SSGRoute.PTExt.Coeff G) (x : X.V) :
    (Work.SSGRoute.PT.freeCoverCompat φ X).hom
        (Finsupp.single x (MonoidAlgebra.single (1 : H) (1 : SSGRoute.PTExt.Coeff)))
      = Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : SSGRoute.PTExt.Coeff)) := by
  rw [Work.SSGRoute.PT.freeCoverCompat, Rep.freeLift, Rep.hom_ofHom,
    Representation.freeLift_single_single]
  simp

end Work.SSGRoute.E1cGeneric
