import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace Commons.Data.Set

theorem ncard_eq_natCard {α : Type*} (s : Set α) [Fintype ↥s] : s.ncard = Nat.card s := by
  exact (Nat.card_coe_set_eq s).symm

end Commons.Data.Set