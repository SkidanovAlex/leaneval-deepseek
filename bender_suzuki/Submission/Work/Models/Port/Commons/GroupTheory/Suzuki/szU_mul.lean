import Mathlib.FieldTheory.Finite.GaloisField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Suzuki

open Matrix

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The field `GF(2^(2n+1))` in which the Suzuki root matrices live. -/
abbrev SzF (n : ℕ) := GaloisField 2 (2 * n + 1)

private lemma sz_two_eq_zero (n : ℕ) : (2 : SzF n) = 0 := by
  have := CharP.cast_eq_zero (SzF n) 2
  simpa using this

/-- The Tits automorphism `x ↦ x^(2^(n+1))` composed with itself is the Frobenius square,
because `x^(2^(2n+1)) = x` in `GF(2^(2n+1))`. -/
private lemma pow_theta_theta (n : ℕ) (x : SzF n) :
    (x ^ (2 ^ (n + 1))) ^ (2 ^ (n + 1)) = x ^ 2 := by
  haveI : Fintype (SzF n) := Fintype.ofFinite _
  have hcard : Fintype.card (SzF n) = 2 ^ (2 * n + 1) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * n + 1) (by omega)]
  rw [← pow_mul]
  have hmm : 2 ^ (n + 1) * 2 ^ (n + 1) = 2 ^ (2 * n + 1) * 2 := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  rw [hmm, pow_mul]
  rw [show x ^ 2 ^ (2 * n + 1) = x by
    rw [← hcard]
    exact FiniteField.pow_card x]

/-- Additivity of `x ↦ x^(2^(n+1))`, in the orientation used for the `(1,2)` entry. -/
private lemma theta_add_comm (n : ℕ) (a c : SzF n) :
    c ^ (2 ^ (n + 1)) + a ^ (2 ^ (n + 1)) = (a + c) ^ (2 ^ (n + 1)) := by
  rw [add_pow_char_pow a c 2 (n + 1)]
  ring

/-- The `(1,3)` entry identity of the Suzuki root-group multiplication law. -/
private lemma entry13 (n : ℕ) (a b c d : SzF n) :
    c ^ (1 + 2 ^ (n + 1)) + d + a ^ (2 ^ (n + 1)) * c + (a ^ (1 + 2 ^ (n + 1)) + b)
      = (a + c) ^ (1 + 2 ^ (n + 1)) + (b + d + a * c ^ (2 ^ (n + 1))) := by
  have h2 : (2 : SzF n) = 0 := sz_two_eq_zero n
  have h1 : (a + c) ^ (1 + 2 ^ (n + 1)) = (a + c) * (a + c) ^ (2 ^ (n + 1)) := by
    rw [pow_add, pow_one]
  rw [h1, add_pow_char_pow a c 2 (n + 1)]
  have ha : a ^ (1 + 2 ^ (n + 1)) = a * a ^ (2 ^ (n + 1)) := by rw [pow_add, pow_one]
  have hc : c ^ (1 + 2 ^ (n + 1)) = c * c ^ (2 ^ (n + 1)) := by rw [pow_add, pow_one]
  rw [ha, hc]
  ring_nf
  simp [h2]

/-- The `(0,3)` entry identity of the Suzuki root-group multiplication law. -/
private lemma entry03 (n : ℕ) (a b c d : SzF n) :
    (a + c) ^ (2 + 2 ^ (n + 1)) + (a + c) * (b + d + a * c ^ (2 ^ (n + 1)))
      + (b + d + a * c ^ (2 ^ (n + 1))) ^ (2 ^ (n + 1))
    = a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1))
      + a * (c ^ (1 + 2 ^ (n + 1)) + d) + b * c
      + (c ^ (2 + 2 ^ (n + 1)) + c * d + d ^ (2 ^ (n + 1))) := by
  have e1 : (a + c) ^ (2 + 2 ^ (n + 1)) = (a + c) ^ 2 * (a + c) ^ (2 ^ (n + 1)) := by
    rw [pow_add]
  have e2 : (a + c) ^ 2 = a ^ 2 + c ^ 2 := add_pow_char a c 2
  have e3 : (a + c) ^ (2 ^ (n + 1)) = a ^ (2 ^ (n + 1)) + c ^ (2 ^ (n + 1)) :=
    add_pow_char_pow a c 2 (n + 1)
  have e4 : (b + d + a * c ^ (2 ^ (n + 1))) ^ (2 ^ (n + 1))
      = b ^ (2 ^ (n + 1)) + d ^ (2 ^ (n + 1)) + a ^ (2 ^ (n + 1)) * c ^ 2 := by
    have h := add_pow_char_pow (b + d) (a * c ^ (2 ^ (n + 1))) 2 (n + 1)
    have h2 := add_pow_char_pow b d 2 (n + 1)
    have h3 : (a * c ^ (2 ^ (n + 1))) ^ (2 ^ (n + 1)) = a ^ (2 ^ (n + 1)) * c ^ 2 := by
      rw [mul_pow, pow_theta_theta]
    rw [h, h2, h3]
  have h2 : (2 : SzF n) = 0 := sz_two_eq_zero n
  rw [e1, e2, e3, e4]
  rw [pow_add, pow_add, pow_add, pow_add]
  ring_nf
  simp [h2]

theorem szU_mul (n : ℕ) (a b c d : GaloisField 2 (2 * n + 1)) :
    !![1, a, b, a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1));
       0, 1, a ^ (2 ^ (n + 1)), a ^ (1 + 2 ^ (n + 1)) + b;
       0, 0, 1, a;
       0, 0, 0, 1] *
    !![1, c, d, c ^ (2 + 2 ^ (n + 1)) + c * d + d ^ (2 ^ (n + 1));
       0, 1, c ^ (2 ^ (n + 1)), c ^ (1 + 2 ^ (n + 1)) + d;
       0, 0, 1, c;
       0, 0, 0, 1] =
    !![1, a + c, b + d + a * c ^ (2 ^ (n + 1)),
         (a + c) ^ (2 + 2 ^ (n + 1)) + (a + c) * (b + d + a * c ^ (2 ^ (n + 1)))
           + (b + d + a * c ^ (2 ^ (n + 1))) ^ (2 ^ (n + 1));
       0, 1, (a + c) ^ (2 ^ (n + 1)),
         (a + c) ^ (1 + 2 ^ (n + 1)) + (b + d + a * c ^ (2 ^ (n + 1)));
       0, 0, 1, a + c;
       0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, theta_add_comm, entry13]
  all_goals first | (rw [entry03]; ring) | ring

end Commons.GroupTheory.Suzuki