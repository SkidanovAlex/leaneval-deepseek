import Mathlib.GroupTheory.Perm.Cycle.Type

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.OrderOfElement

theorem odd_card_iff_forall_orderOf_ne_two {G : Type*} [Group G] [Finite G] :
    Odd (Nat.card G) ↔ ∀ g : G, orderOf g ≠ 2 := by
  constructor
  · intro h g hg
    have h2 : 2 ∣ Nat.card G := by rw [← hg]; exact orderOf_dvd_natCard g
    exact h.not_two_dvd_nat h2
  · intro h
    by_contra hne
    have h2 : 2 ∣ Nat.card G := (Nat.not_odd_iff_even.mp hne).two_dvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    exact h x hx

end Commons.GroupTheory.OrderOfElement