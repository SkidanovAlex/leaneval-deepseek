import Mathlib.GroupTheory.Index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Conjugation

/-- The cardinality of the conjugacy class of `g` equals the index of the centralizer of `g`.

This is the orbit–stabilizer theorem for the conjugation action of `G` on itself, together with
the identification of the stabilizer of `g` under conjugation with the centralizer of `g`. -/
theorem card_conjClass_eq_index_centralizer {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier = (Subgroup.centralizer ({g} : Set G)).index := by
  -- The conjugacy class of `g` is the orbit of `g` under the conjugation action.
  have h1 : Nat.card (ConjClasses.mk g).carrier =
      (MulAction.stabilizer (ConjAct G) g).index := by
    rw [← ConjAct.orbit_eq_carrier_conjClasses g]
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  -- The stabilizer of `g` under conjugation is the centralizer of `g`.
  have h2 : (Subgroup.centralizer ({g} : Set G)).index =
      (MulAction.stabilizer (ConjAct G) g).index := by
    rw [Subgroup.centralizer_eq_comap_stabilizer g]
    exact Subgroup.index_comap_of_surjective _ ConjAct.toConjAct.surjective
  exact h1.trans h2.symm

end Commons.GroupTheory.Conjugation