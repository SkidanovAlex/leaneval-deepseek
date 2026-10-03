import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_count_eq_fin_count
import Submission.Commons.NumberTheory.FriedlanderIwaniec.nat_sq_neg_one_count_succ_eq
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_eq_two

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The number of solutions of `x ^ 2 + 1 ≡ 0 (mod p ^ e)` is the same for all
`e ≥ 1`, when `p` is an odd prime. This is the iterate of
`nat_sq_neg_one_count_succ_eq`. -/
lemma nat_sq_neg_one_count_pow_eq_pow_one {p e : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (he : 1 ≤ e) :
    ({x : Fin (p ^ e) | p ^ e ∣ (x : ℕ) ^ 2 + 1}.ncard) =
      ({x : Fin p | p ∣ (x : ℕ) ^ 2 + 1}.ncard) := by
  have aux : ∀ k, 1 ≤ k →
      ({x : Fin (p ^ k) | p ^ k ∣ (x : ℕ) ^ 2 + 1}.ncard) =
        ({x : Fin p | p ∣ (x : ℕ) ^ 2 + 1}.ncard) := by
    intro k
    refine Nat.le_induction ?base ?step k
    · rw [pow_one]
    · intro m hm ih
      exact (nat_sq_neg_one_count_succ_eq hp hpodd hm).trans ih
  exact aux e he

theorem sq_roots_neg_one_mod_prime_pow_eq_two {p e : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (he : 1 ≤ e) : ({α : ZMod (p ^ e) | α ^ 2 = -1}.ncard) = 2 := by
  have hpodd : p ≠ 2 := by
    intro h
    rw [h] at hp4
    norm_num at hp4
  have hpos : 0 < p ^ e := pow_pos hp.pos e
  rw [sq_roots_neg_one_count_eq_fin_count (n := p ^ e) hpos]
  rw [nat_sq_neg_one_count_pow_eq_pow_one hp hpodd he]
  rw [← sq_roots_neg_one_count_eq_fin_count (n := p) hp.pos]
  exact sq_roots_neg_one_mod_prime_eq_two hp hp4

end Commons.NumberTheory.FriedlanderIwaniec
