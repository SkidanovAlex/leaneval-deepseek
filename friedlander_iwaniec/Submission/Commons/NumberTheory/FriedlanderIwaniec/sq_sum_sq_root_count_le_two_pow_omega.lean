import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_eq_gcd_mul
import Submission.Commons.NumberTheory.FriedlanderIwaniec.rho_le_two_pow_omega

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- Upper bound for the number of roots of `X ^ 2 + b ^ 2` modulo `d`:
it is at most `2 ^ ω(d)` times `gcd (b, ∏_{p | d} p ^ (v_p d / 2))`.

This combines the exact count identity (which factors out the `gcd` and leaves a
count of square roots of `-1` modulo `d / gcd (b ^ 2) d`) with the bound
`2 ^ ω` for the number of square roots of `-1` modulo any positive modulus. -/
theorem sq_sum_sq_root_count_le_two_pow_omega {d b : ℕ} (hd : 0 < d) :
    ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0}.ncard) ≤
      2 ^ (Nat.primeFactors d).card *
        Nat.gcd b ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) := by
  classical
  rw [sq_sum_sq_root_count_eq_gcd_mul hd]
  set g := Nat.gcd (b ^ 2) d with hg
  have hgdvd : g ∣ d := Nat.gcd_dvd_right _ _
  have hgle : g ≤ d := Nat.le_of_dvd hd hgdvd
  have hgpos0 : 0 < g := Nat.pos_of_dvd_of_pos hgdvd hd
  have hgpos : 0 < d / g := Nat.div_pos hgle hgpos0
  -- bound the number of square roots of `-1` modulo `d / g`
  have hM : ({α : ZMod (d / g) | α ^ 2 = -1}.ncard) ≤ 2 ^ (Nat.primeFactors (d / g)).card :=
    rho_le_two_pow_omega hgpos
  -- the prime factors of `d / g` are among those of `d`
  have hsub : Nat.primeFactors (d / g) ⊆ Nat.primeFactors d :=
    Nat.primeFactors_mono (Nat.div_dvd_of_dvd hgdvd) hd.ne'
  have hcard : (Nat.primeFactors (d / g)).card ≤ (Nat.primeFactors d).card :=
    Finset.card_le_card hsub
  have h2 : 2 ^ (Nat.primeFactors (d / g)).card ≤ 2 ^ (Nat.primeFactors d).card :=
    Nat.pow_le_pow_right (by norm_num) hcard
  calc Nat.gcd b ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) *
        ({α : ZMod (d / g) | α ^ 2 = -1}.ncard)
      ≤ Nat.gcd b ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) *
          2 ^ (Nat.primeFactors d).card :=
        Nat.mul_le_mul_left _ (le_trans hM h2)
    _ = 2 ^ (Nat.primeFactors d).card *
          Nat.gcd b ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) :=
        Nat.mul_comm _ _

end Commons.NumberTheory.FriedlanderIwaniec
