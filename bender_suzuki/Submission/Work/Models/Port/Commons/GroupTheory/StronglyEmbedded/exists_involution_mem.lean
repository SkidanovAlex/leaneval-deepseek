import Mathlib.GroupTheory.Perm.Cycle.Type

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem exists_involution_mem {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hEven : Even (Nat.card M)) : ∃ t ∈ M, orderOf t = 2 := by
  have h2 : 2 ∣ Nat.card M := even_iff_two_dvd.mp hEven
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 h2
  exact ⟨(t : G), t.2, by rw [Subgroup.orderOf_coe]; exact ht⟩

end Commons.GroupTheory.StronglyEmbedded