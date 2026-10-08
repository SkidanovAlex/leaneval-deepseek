import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Conjugation.card_conjClass_eq_index_centralizer
import Submission.Work.Models.Port.Commons.GroupTheory.Conjugation.card_involutions_eq_index_centralizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Conjugation

theorem exists_conj_eq_of_card_conjClass_eq_of_orderOf_eq_two {G : Type*} [Group G] [Finite G]
    (u : G) (hu : orderOf u = 2)
    (hcard : Nat.card (ConjClasses.mk u).carrier = Nat.card {t : G // orderOf t = 2}) :
    ∀ t : G, orderOf t = 2 → ∃ z : G, z * u * z⁻¹ = t := by
  classical
  -- Every element of the conjugacy class of `u` is an involution.
  have hsub : (ConjClasses.mk u).carrier ⊆ {t : G | orderOf t = 2} := by
    intro v hv
    rw [ConjClasses.mem_carrier_iff_mk_eq] at hv
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hv
    obtain ⟨c, hc⟩ := hv
    change orderOf v = 2
    rw [← orderOf_conjugate_eq c v, hc, hu]
  -- The two sets have the same cardinality, so they are equal.
  have hcard' : (ConjClasses.mk u).carrier.ncard = {t : G | orderOf t = 2}.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hset : (ConjClasses.mk u).carrier = {t : G | orderOf t = 2} :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard'.symm)
  -- Hence every involution lies in the conjugacy class of `u`.
  intro t ht
  have htA : t ∈ (ConjClasses.mk u).carrier := by rw [hset]; exact ht
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at htA
  exact isConj_iff.mp (IsConj.symm htA)

end Commons.GroupTheory.Conjugation
