import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Choose.Sum

namespace Commons.Data.Nat

theorem sum_powerset_neg_one_pow_card_real (x : Finset ℕ) :
    (∑ m ∈ x.powerset, ((-1 : ℝ) ^ m.card)) = if x = ∅ then (1 : ℝ) else 0 := by
  exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := x))

end Commons.Data.Nat