import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_eq_two
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_eq_zero
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_two_eq_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

lemma sq_roots_neg_one_mod_prime_pow_eq_one_add_chi4 {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (h4 : ¬ 4 ∣ p ^ e) :
    (({α : ZMod (p ^ e) | α ^ 2 = -1}.ncard : ℕ) : ℤ) = 1 + ZMod.χ₄ (p : ZMod 4) := by
  rcases hp.eq_two_or_odd with hp2 | hpodd
  · subst hp2
    have he1 : e = 1 := by
      by_contra hne
      have h2 : 2 ≤ e := by omega
      exact h4 (by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact pow_dvd_pow 2 h2)
    subst he1
    rw [pow_one, sq_roots_neg_one_mod_two_eq_one]
    rw [ZMod.χ₄_nat_eq_if_mod_four (2 : ℕ)]
    norm_num
  · rcases Nat.odd_mod_four_iff.mp hpodd with h1 | h3
    · rw [sq_roots_neg_one_mod_prime_pow_eq_two hp h1 he, ZMod.χ₄_nat_one_mod_four h1]
      norm_num
    · rw [sq_roots_neg_one_mod_prime_pow_eq_zero hp h3 he, ZMod.χ₄_nat_three_mod_four h3]
      norm_num

end Commons.NumberTheory.FriedlanderIwaniec
