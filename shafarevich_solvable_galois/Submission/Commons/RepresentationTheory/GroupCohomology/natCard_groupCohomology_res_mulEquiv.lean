import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory

/-- Group cohomology is invariant under restricting a representation along a group
isomorphism: the underlying vector space does not change, only the action is
transported along `e`. -/
theorem natCard_groupCohomology_res_mulEquiv {k G G' : Type} [CommRing k] [Group G] [Group G']
    (e : G ≃* G') (A : Rep.{0,0,0} k G') (n : ℕ) :
    Nat.card (groupCohomology (Rep.res e.toMonoidHom A) n) = Nat.card (groupCohomology A n) := by
  refine Nat.card_congr (CategoryTheory.Iso.toLinearEquiv
    (groupCohomology.mapIso (G := G) (H := G') (A := A) (B := Rep.res e.toMonoidHom A) e
      (LinearEquiv.refl k A.V) ?_ n)).toEquiv
  intro g
  rfl

end Commons.RepresentationTheory.GroupCohomology