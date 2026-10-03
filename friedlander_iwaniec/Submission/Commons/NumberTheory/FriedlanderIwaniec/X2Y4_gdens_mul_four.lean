import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The number of solutions of `x ^ 2 + y ^ 4 = 0` in `ZMod 4 × ZMod 4` is `4`:
modulo `4` both `x ^ 2` and `y ^ 4` lie in `{0, 1}`, so a solution forces
`x ^ 2 = y ^ 4 = 0`, i.e. `x` and `y` even.

This is the case `p = 2` of `X2Y4_pair_roots_mod_prime_sq_card`, unpacked. -/
lemma X2Y4_N_four : Submission.N 4 = 4 := by
  have h := X2Y4_pair_roots_mod_prime_sq_card Nat.prime_two
  simp only [Submission.N]
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at h
  rw [h]
  norm_num

/-- `4` is coprime to `m` whenever `m` is odd, i.e. `2 ∤ m`. -/
lemma X2Y4_coprime_four_of_not_two_dvd {m : ℕ} (hm : ¬ 2 ∣ m) : Nat.Coprime 4 m := by
  have h : (2 ^ 2).Coprime m := by
    rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm
  simpa using h

/-- The local density `g(d) = N(d)/d²`, `N(d) = #{(x₁,x₂) ∈ (ZMod d)² : x₁² + x₂⁴ = 0}`
is multiplicative, and at `4` it equals `1/4`:  hence for odd `m`, `g (4 * m) = 1/4 * g m`.
(Also `g 4 = 1/4` and `g 2 = 1/2`.) -/
theorem X2Y4_gdens_mul_four (m : ℕ) (hm : ¬ 2 ∣ m) :
    (Submission.gdens (4 * m) : ℝ) = 1 / 4 * (Submission.gdens m : ℝ) := by
  have hcop : Nat.Coprime 4 m := X2Y4_coprime_four_of_not_two_dvd hm
  have hmul : Submission.gdens (4 * m) = 1 / 4 * Submission.gdens m := by
    rw [Submission.gdens_mul_of_coprime hcop, Submission.gdens_four]
  rw [hmul]
  push_cast
  ring

end Commons.NumberTheory.FriedlanderIwaniec
