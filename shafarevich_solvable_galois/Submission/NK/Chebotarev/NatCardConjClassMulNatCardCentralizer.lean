import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.Chebotarev

/-- The conjugacy class of `g` has cardinality the index of its centralizer, so its cardinality
times that of the centralizer is the order of the group. -/
theorem NatCardConjClassMulNatCardCentralizer {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card {x : G // IsConj x g} * Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have h1 : Nat.card {x : G // IsConj x g} = Nat.card ↑(MulAction.orbit (ConjAct G) g) :=
    Nat.card_congr
      (Equiv.subtypeEquivRight fun x => (ConjAct.mem_orbit_conjAct (g := x) (h := g)).symm)
  rw [h1, Subgroup.nat_card_centralizer_nat_card_stabilizer]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← ConjAct.card]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g

end NK.Chebotarev
