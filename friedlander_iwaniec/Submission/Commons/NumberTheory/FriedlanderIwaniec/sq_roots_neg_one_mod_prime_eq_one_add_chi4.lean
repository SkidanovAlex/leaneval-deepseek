import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_card_value
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_two_eq_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

lemma sq_roots_neg_one_mod_prime_eq_one_add_chi4 {p : ℕ} (hp : p.Prime) :
    (({α : ZMod p | α ^ 2 = -1}.ncard : ℕ) : ℤ) = 1 + ZMod.χ₄ (p : ZMod 4) := by
  rw [sq_roots_neg_one_mod_prime_card_value hp]
  rw [ZMod.χ₄_nat_eq_if_mod_four p]
  rcases hp.eq_two_or_odd with hp2 | hodd
  · subst hp2
    norm_num
  · rcases Nat.odd_mod_four_iff.mp hodd with h1 | h3
    · rw [if_pos h1, if_neg (by omega : ¬ p % 2 = 0), if_pos h1]
      norm_num
    · rw [if_neg (by omega : ¬ p % 4 = 1), if_neg (by omega : ¬ p = 2),
          if_neg (by omega : ¬ p % 2 = 0), if_neg (by omega : ¬ p % 4 = 1)]
      norm_num

end Commons.NumberTheory.FriedlanderIwaniec
