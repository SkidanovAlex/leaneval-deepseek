import Mathlib
import Submission.Work.ORFP2.CosetProj

set_option autoImplicit false

namespace Work.ORFP2

variable (k : Type*) [CommRing k] {G : Type*} [Group G]

/-- `transferHom` is `MonoidAlgebra.mapDomain` along the subtype inclusion `H ↪ G`. -/
lemma transferHom_eq_mapDomain (H : Subgroup G) (a : MonoidAlgebra k H) :
    transferHom k H a = MonoidAlgebra.mapDomain H.subtype a :=
  rfl

/-- The `k[H]`-component of `transferHom k H a` is `a`: the algebra inclusion `k[H] ↪ k[G]`
is a section of the projection `projH k H`. -/
theorem projH_transferHom (k : Type*) [CommRing k] {G : Type*} [Group G] (H : Subgroup G)
    (a : MonoidAlgebra k H) : projH k H (transferHom k H a) = a := by
  ext h
  rw [projH_coeff k H _ (h : G) h.2]
  show (transferHom k H a).coeff (h : G) = a.coeff h
  rw [transferHom_eq_mapDomain]
  show (Finsupp.mapDomain (⇑H.subtype) a.coeff) (↑h) = a.coeff h
  exact Finsupp.mapDomain_apply_of_injective H.subtype_injective a.coeff h

end Work.ORFP2
