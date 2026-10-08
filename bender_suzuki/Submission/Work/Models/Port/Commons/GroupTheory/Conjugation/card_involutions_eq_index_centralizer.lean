import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Conjugation

/-- Conjugation by an element preserves the order of an element. -/
lemma orderOf_conjugate_eq {G : Type*} [Group G] (z x : G) :
    orderOf (z * x * z⁻¹) = orderOf x := by
  exact (SemiconjBy.orderOf_eq z (by
    dsimp [SemiconjBy]
    group)).symm

theorem card_involutions_eq_index_centralizer {G : Type*} [Group G] [Finite G]
    (u : G) (hu : orderOf u = 2)
    (hsingle : ∀ t : G, orderOf t = 2 → ∃ z : G, z * u * z⁻¹ = t) :
    Nat.card {t : G // orderOf t = 2} = (Subgroup.centralizer ({u} : Set G)).index := by
  classical
  -- The set of involutions is exactly the orbit of `u` under conjugation.
  have hset : {t : G | orderOf t = 2} = MulAction.orbit (ConjAct G) u := by
    ext t
    constructor
    · intro ht
      rw [ConjAct.mem_orbit_conjAct]
      exact (isConj_comm.mp (isConj_iff.mpr (hsingle t ht)))
    · intro ht
      rw [ConjAct.mem_orbit_conjAct] at ht
      rcases ht with ⟨z, hz⟩
      simpa [hu] using (SemiconjBy.orderOf_eq (z : G) hz)
  -- The index of the centralizer of `u` in `G` equals the index of the stabilizer
  -- of `u` under the conjugation action of `ConjAct G`.
  have hindex : (Subgroup.centralizer ({u} : Set G)).index =
      (MulAction.stabilizer (ConjAct G) u).index := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    exact Subgroup.index_comap_of_surjective (MulAction.stabilizer (ConjAct G) u)
      (f := ConjAct.toConjAct.toMonoidHom) (by
        intro x
        exact ⟨ConjAct.ofConjAct x, by simp⟩)
  calc
    Nat.card {t : G // orderOf t = 2} = ({t : G | orderOf t = 2}).ncard := by
      exact Nat.card_coe_set_eq {t : G | orderOf t = 2}
    _ = (MulAction.orbit (ConjAct G) u).ncard := by rw [hset]
    _ = (MulAction.stabilizer (ConjAct G) u).index := by
      exact (MulAction.index_stabilizer (ConjAct G) u).symm
    _ = (Subgroup.centralizer ({u} : Set G)).index := hindex.symm

end Commons.GroupTheory.Conjugation