import Mathlib

namespace Work.LT

theorem gb_gaussian_prod_pos (j : ℕ) :
    0 < ∏ i : Fin j, ((2:ℕ)^j - 2^(i:ℕ)) := by
  exact Finset.prod_pos fun i _ => Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) i.isLt)

end Work.LT
