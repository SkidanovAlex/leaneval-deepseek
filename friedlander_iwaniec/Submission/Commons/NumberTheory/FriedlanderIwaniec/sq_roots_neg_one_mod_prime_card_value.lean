import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_eq_zero
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_eq_two
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_two_eq_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

lemma sq_roots_neg_one_mod_prime_card_value {p : ℕ} (hp : p.Prime) :
    ({α : ZMod p | α ^ 2 = -1}.ncard) = if p % 4 = 1 then 2 else if p = 2 then 1 else 0 := by
  rcases hp.eq_two_or_odd with hp2 | hodd
  · rw [hp2]
    norm_num
  · rcases Nat.odd_mod_four_iff.mp hodd with h1 | h3
    · rw [if_pos h1]
      exact sq_roots_neg_one_mod_prime_eq_two hp h1
    · have hp1 : ¬ p % 4 = 1 := by omega
      have hpne2 : ¬ p = 2 := by omega
      rw [if_neg hp1, if_neg hpne2]
      exact sq_roots_neg_one_mod_prime_eq_zero hp h3

end Commons.NumberTheory.FriedlanderIwaniec
