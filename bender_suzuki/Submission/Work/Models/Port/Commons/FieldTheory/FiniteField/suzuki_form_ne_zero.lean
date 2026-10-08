import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.galoisField_pow_two_pow_succ_succ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.FieldTheory.FiniteField

/-- **Suzuki form is anisotropic.**  Let `K` be a field of characteristic `2` and suppose that
the `k`-fold Frobenius squaring map `x ↦ x ^ 2 ^ k` is an involution *up to* the ordinary
squaring, i.e. `(x ^ 2 ^ k) ^ 2 ^ k = x ^ 2` for every `x : K`.  Then the Suzuki form
`(a, b) ↦ a ^ (2 + 2 ^ k) + a * b + b ^ (2 ^ k)` has no nonzero zero over `K`.

The proof normalises `a` to `1` using the homogeneity substitution
`(a, b) ↦ (λ * a, λ ^ (1 + 2 ^ k) * b)`, which multiplies the form by `λ ^ (2 + 2 ^ k)`.
-/
theorem suzuki_form_ne_zero_aux {K : Type*} [Field K] [CharP K 2]
    (k : ℕ) (a b : K) (hF : ∀ x : K, (x ^ 2 ^ k) ^ 2 ^ k = x ^ 2) :
    a ^ (2 + 2 ^ k) + a * b + b ^ (2 ^ k) = 0 → a = 0 ∧ b = 0 := by
  intro h
  have hk0 : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hkpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hk2 : 2 + 2 ^ k ≠ 0 := by omega
  by_cases ha : a = 0
  · subst ha
    have hb : b ^ (2 ^ k) = 0 := by simpa [zero_pow hk2] using h
    exact ⟨rfl, (pow_eq_zero_iff hk0).mp hb⟩
  · exfalso
    -- Rearrange the hypothesis: `a * b + b ^ 2 ^ k = a ^ (2 + 2 ^ k)`.
    have h2 : a * b + b ^ (2 ^ k) = a ^ (2 + 2 ^ k) := by
      rw [add_assoc] at h
      have hh := eq_neg_of_add_eq_zero_right h
      rwa [CharTwo.neg_eq] at hh
    have hPne : a * a ^ (2 ^ k) ≠ 0 := mul_ne_zero ha (pow_ne_zero _ ha)
    have hQne : a ^ (2 + 2 ^ k) ≠ 0 := pow_ne_zero _ ha
    -- `(a * a ^ 2 ^ k) ^ 2 ^ k = a ^ (2 + 2 ^ k)`.
    have hPs : (a * a ^ (2 ^ k)) ^ (2 ^ k) = a ^ (2 + 2 ^ k) := by
      rw [mul_pow, hF a, ← pow_add]
      congr 1
      omega
    -- The normalisation: `c = b / (a * a ^ 2 ^ k)`.
    set c : K := b / (a * a ^ (2 ^ k)) with hc
    have hQc : a ^ (2 + 2 ^ k) * c = a * b := by
      rw [hc, pow_add, pow_two,
        show (a * a) * a ^ (2 ^ k) = a * (a * a ^ (2 ^ k)) by ring, mul_assoc,
        mul_div_cancel₀ b hPne]
    have hQcs : a ^ (2 + 2 ^ k) * c ^ (2 ^ k) = b ^ (2 ^ k) := by
      rw [hc, div_pow, hPs]
      exact mul_div_cancel₀ (b ^ (2 ^ k)) hQne
    -- Normalised equation.
    have hcc : c + c ^ (2 ^ k) = 1 := by
      have key : a ^ (2 + 2 ^ k) * (c + c ^ (2 ^ k)) = a ^ (2 + 2 ^ k) * 1 := by
        rw [mul_add, hQc, hQcs, mul_one, h2]
      exact mul_left_cancel₀ hQne key
    -- Apply the `k`-fold Frobenius to the normalised equation.
    have hpow : (c + c ^ (2 ^ k)) ^ (2 ^ k) = c ^ (2 ^ k) + (c ^ (2 ^ k)) ^ (2 ^ k) :=
      add_pow_char_pow c (c ^ (2 ^ k)) 2 k
    have hcc2 : c ^ (2 ^ k) + c ^ 2 = 1 := by
      rw [← hF c, ← hpow, hcc, one_pow]
    -- Hence `c = c ^ 2`, so `c` lies in the prime field `{0, 1}`.
    have hceq : c = c ^ 2 := by
      have h1 : c ^ (2 ^ k) + c = 1 := by rw [add_comm, hcc]
      exact add_left_cancel (h1.trans hcc2.symm)
    have hc01 : c = 0 ∨ c = 1 := by
      have hmul : c * (c - 1) = 0 := by
        rw [mul_sub, mul_one, ← pow_two, ← hceq, sub_self]
      rcases mul_eq_zero.mp hmul with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h1)
    -- But then `c + c ^ 2 ^ k = 0 ≠ 1`.
    rcases hc01 with h0 | h1
    · rw [h0, zero_pow hk0, zero_add] at hcc
      exact zero_ne_one hcc
    · rw [h1, one_pow] at hcc
      have h10 : (1 : K) = 0 := add_left_cancel (by rw [add_zero]; exact hcc)
      exact one_ne_zero h10

theorem suzuki_form_ne_zero (n : ℕ) (a b : GaloisField 2 (2 * n + 1)) :
    a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)) = 0 → a = 0 ∧ b = 0 :=
  suzuki_form_ne_zero_aux (n + 1) a b fun x => galoisField_pow_two_pow_succ_succ n x

end Commons.FieldTheory.FiniteField