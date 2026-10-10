import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Submission.Work.SSGRoute.freeAssocMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

@[simp] theorem freeAssocMap_wordEl {X : Type*} (σ : X ≃ X) (w : List X) :
    Work.SSGRoute.prop5.freeAssocMap σ (Work.SSGRoute.prop5.wordEl w)
      = Work.SSGRoute.prop5.wordEl (w.map σ) := by
  simp only [Work.SSGRoute.prop5.freeAssocMap, Work.SSGRoute.prop5.wordEl,
    MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  rfl

end Work.SSGRoute
