/-
# The free-group basis instance

`Work.ORFP2.FreeGroupAugIdealBasis k` holds: the augmentation ideal of the group algebra of a free
group is free on the elements `x - 1`.
-/
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFP2.FreeBasisAssembly

set_option autoImplicit false

universe u

namespace Work.ORFP2

/-- The free-group augmentation basis, with the universe of the generating set tied to that of `k`
so that it can be applied without leaving universe metavariables. -/
theorem freeGroupAugIdealBasis_inst (k : Type u) [CommRing k] :
    FreeGroupAugIdealBasis.{u, u} k :=
  fun α _ => freeGroupAugIdealBasis_assembled.{u, u} k α

end Work.ORFP2
