import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_pow_card_mod_four_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- For a fixed `y` in `ZMod (p ^ e)` the number of `x` with `x ^ 2 + y ^ 4 = 0`
is at most `2 * p ^ (e / 2)`.

This is the general root-count estimate `sq_sum_sq_root_count_le_two_pow_omega`
specialised to the modulus `p ^ e`: the number of prime factors is one, the square
part is `p ^ (e / 2)`, and the remaining `gcd` factor is at most `p ^ (e / 2)`. -/
lemma X2Y4_fiber_ncard_le {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (y : ZMod (p ^ e)) :
    ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0}).ncard ≤ 2 * p ^ (e / 2) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  set b : ℕ := (y ^ 2).val with hb
  have hbcast : (b : ZMod (p ^ e)) = y ^ 2 := ZMod.natCast_zmod_val (y ^ 2)
  have hy4 : y ^ 4 = (b : ZMod (p ^ e)) ^ 2 := by rw [hbcast]; ring
  have hset : ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0} : Set (ZMod (p ^ e)))
      = {x : ZMod (p ^ e) | x ^ 2 + (b : ZMod (p ^ e)) ^ 2 = 0} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hy4]
  rw [hset]
  have hd : 0 < p ^ e := pow_pos hp.pos e
  have hmain := sq_sum_sq_root_count_le_two_pow_omega (d := p ^ e) (b := b) hd
  have hcard1 : (Nat.primeFactors (p ^ e)).card = 1 := by
    rw [Nat.primeFactors_prime_pow (k := e) (by omega : e ≠ 0) hp, Finset.card_singleton]
  have hprod : (Nat.primeFactors (p ^ e)).prod
        (fun q => q ^ ((p ^ e).factorization q / 2)) = p ^ (e / 2) := by
    rw [Nat.primeFactors_prime_pow (k := e) (by omega : e ≠ 0) hp, Finset.prod_singleton]
    have hfac : (p ^ e).factorization p = e := by
      rw [Nat.Prime.factorization_pow hp]
      exact Finsupp.single_eq_same
    rw [hfac]
  calc ({x : ZMod (p ^ e) | x ^ 2 + (b : ZMod (p ^ e)) ^ 2 = 0}).ncard
      ≤ 2 ^ (Nat.primeFactors (p ^ e)).card *
          Nat.gcd b ((Nat.primeFactors (p ^ e)).prod
            (fun q => q ^ ((p ^ e).factorization q / 2))) := hmain
    _ = 2 * Nat.gcd b (p ^ (e / 2)) := by rw [hcard1, hprod, pow_one]
    _ ≤ 2 * p ^ (e / 2) :=
        Nat.mul_le_mul_left 2 (Nat.gcd_le_right b (pow_pos hp.pos (e / 2)))

theorem X2Y4_pair_ncard_prime_pow_le {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    ({x : ZMod (p ^ e) × ZMod (p ^ e) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard
      ≤ 2 * p ^ (e + e / 2) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [X2Y4_ncard_eq_sum_fiber (p := p) (e := e)]
  calc ∑ y : ZMod (p ^ e), ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0}).ncard
      ≤ ∑ _y : ZMod (p ^ e), 2 * p ^ (e / 2) :=
        Finset.sum_le_sum (fun y _ => X2Y4_fiber_ncard_le hp he y)
    _ = p ^ e * (2 * p ^ (e / 2)) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    _ = 2 * p ^ (e + e / 2) := by rw [pow_add]; ring

end Commons.NumberTheory.FriedlanderIwaniec
