import Mathlib.GroupTheory.Torsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalTame.Transfer

/-- Isomorphic commutative groups have torsion subgroups of the same cardinality. -/
theorem natCard_torsion_mulEquiv {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    Nat.card (CommGroup.torsion A) = Nat.card (CommGroup.torsion B) := by
  rw [← e.map_torsion]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective (CommGroup.torsion A) (e : A →* B) e.injective).toEquiv

end NK.LocalTame.Transfer
