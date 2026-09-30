import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem card_eqnS (S : ℕ) :
    Fintype.card {s : ℤ // s ∈ Finset.Icc (-(S : ℤ)) S} = 2 * S + 1 := by
  rw [Fintype.card_coe, Int.card_Icc]
  omega

end Work.BW
