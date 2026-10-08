import Mathlib

namespace Work.BG

/-- The conjugacy class of `x`, i.e. the set of elements conjugate to `x`, has
cardinality equal to the index of the centralizer of `x`. -/
theorem conjClassCard {K : Type} [Group K] [Fintype K] (x : K) :
    Nat.card {y : K // IsConj y x} = (Subgroup.centralizer ({x} : Set K)).index := by
  -- Mathlib knows `(centralizer {x}).index = (conjugatesOf x).ncard`.
  rw [Subgroup.index_centralizer_eq_ncard]
  -- Rewrite the right-hand side as the cardinality of the corresponding subtype,
  -- and conjugate the relation to match `conjugatesOf x`'s argument order.
  rw [← Nat.card_coe_set_eq (conjugatesOf x)]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun y => isConj_comm))

end Work.BG
