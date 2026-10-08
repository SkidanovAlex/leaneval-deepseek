import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step4

/-- **Orbit–stabiliser for the conjugation action.**  For an element `z` of a finite group `G`,
the size of the conjugacy class of `z` times the order of its centraliser is `|G|`.

Proof: `G` acts on itself by conjugation via the group `ConjAct G`, the orbit of `z` is the
carrier of `ConjClasses.mk z` (`ConjAct.orbit_eq_carrier_conjClasses`) and the stabiliser of `z`
has the same cardinality as `C_G(z)` (`Subgroup.nat_card_centralizer_nat_card_stabilizer`).  The
orbit–stabiliser theorem (`MulAction.orbitProdStabilizerEquivGroup`) then yields the claim. -/
theorem card_conjClass_mul_card_centralizer {G : Type*} [Group G] [Finite G] (z : G) :
    Nat.card (ConjClasses.mk z).carrier * Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = Nat.card G := by
  have hstab : Nat.card ↥(Subgroup.centralizer ({z} : Set G)) =
      Nat.card ↥(MulAction.stabilizer (ConjAct G) z) :=
    Subgroup.nat_card_centralizer_nat_card_stabilizer z
  have horbit : Nat.card (ConjClasses.mk z).carrier =
      Nat.card ↥(MulAction.orbit (ConjAct G) z) := by
    rw [ConjAct.orbit_eq_carrier_conjClasses]
  have hkey : Nat.card ↥(MulAction.orbit (ConjAct G) z) *
      Nat.card ↥(MulAction.stabilizer (ConjAct G) z) = Nat.card (ConjAct G) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) z)
  have hconj : Nat.card (ConjAct G) = Nat.card G := by simp [Nat.card, ConjAct]
  rw [horbit, hstab, hkey, hconj]

end Work.Hering.Step4
