import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_le_two
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_eq_prod_factorization
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_two_pow_eq_zero
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_two_eq_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

theorem rho_le_two_pow_omega {d : ℕ} (hd : 0 < d) : ({α : ZMod d | α ^ 2 = -1}.ncard) ≤ 2 ^ (Nat.primeFactors d).card := by
  classical
  have hd0 : d ≠ 0 := hd.ne'
  rw [sq_roots_neg_one_eq_prod_factorization hd]
  calc (Nat.primeFactors d).prod
          (fun p => ({α : ZMod (p ^ d.factorization p) | α ^ 2 = -1}.ncard))
      ≤ (Nat.primeFactors d).prod (fun _ => 2) := by
        apply Finset.prod_le_prod₀
        · intro p _
          exact Nat.zero_le _
        · intro p hp
          have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hpdvd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
          have he : 1 ≤ d.factorization p :=
            (hpprime.dvd_iff_one_le_factorization hd0).mp hpdvd
          rcases hpprime.eq_two_or_odd with h2 | hodd
          · subst h2
            rcases (by omega : d.factorization 2 = 1 ∨ 2 ≤ d.factorization 2) with h | h
            · rw [h, pow_one, sq_roots_neg_one_mod_two_eq_one]
              norm_num
            · rw [sq_roots_neg_one_mod_two_pow_eq_zero h]
              omega
          · have hpodd : p ≠ 2 := by rintro rfl; omega
            exact sq_roots_neg_one_mod_prime_pow_le_two hpprime hpodd he
    _ = 2 ^ (Nat.primeFactors d).card := by
        rw [Finset.prod_const]

end Commons.NumberTheory.FriedlanderIwaniec
