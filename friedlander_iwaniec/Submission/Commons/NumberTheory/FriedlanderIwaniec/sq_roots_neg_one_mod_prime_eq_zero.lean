import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

theorem sq_roots_neg_one_mod_prime_eq_zero {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ({α : ZMod p | α ^ 2 = -1}.ncard) = 0 := by
  have h_empty : {α : ZMod p | α ^ 2 = -1} = (∅ : Set (ZMod p)) := by
    ext α
    constructor
    · intro hα
      exact (@ZMod.mod_four_ne_three_of_sq_eq_neg_one p ⟨hp⟩ α hα) hp4
    · simp
  rw [h_empty]
  simp

end Commons.NumberTheory.FriedlanderIwaniec