import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Basic

namespace Commons.Data.Nat

/-- `c / p ^ (j+1) = (c / p) / p ^ j`: shifting off one base-`p` digit. -/
lemma div_pow_succ (p c j : ℕ) : c / p ^ (j + 1) = (c / p) / p ^ j := by
  rw [pow_succ', Nat.div_div_eq_div_mul]

/-- Arithmetic identity: `(p-1) + p*(p^l - 1) = p^(l+1) - 1` for `p ≥ 1`. -/
lemma pred_add_mul_pred (p l : ℕ) (hp : 1 ≤ p) :
    (p - 1) + p * (p ^ l - 1) = p ^ (l + 1) - 1 := by
  have h1 : 1 ≤ p ^ l := Nat.one_le_pow l p (by omega)
  have hpl : p ≤ p * p ^ l := by
    calc p = p * 1 := (mul_one p).symm
      _ ≤ p * p ^ l := Nat.mul_le_mul_left p h1
  have hN : p * p ^ l = p ^ (l + 1) := (pow_succ' p l).symm
  have hbound : p ≤ p ^ (l + 1) := by rw [← hN]; exact hpl
  rw [Nat.mul_sub_left_distrib, mul_one, hN]
  omega

/-- Digit decomposition of the low part: `c % p^(l+1) = c % p + p * (c/p % p^l)`. -/
lemma mod_pow_succ_eq (p l c : ℕ) :
    c % p ^ (l + 1) = c % p + p * (c / p % p ^ l) := by
  have h1 : c % p ^ (l + 1) / p = c / p % p ^ l := by
    have h := Nat.mod_mul_right_div_self c p (p ^ l)
    rwa [← pow_succ'] at h
  have h2 : c % p ^ (l + 1) % p = c % p := by
    rw [Nat.mod_mod_of_dvd c ⟨p ^ l, pow_succ' p l⟩]
  rw [← Nat.div_add_mod (c % p ^ (l + 1)) p, h1, h2]
  exact add_comm _ _

/-- Uniqueness of the representation `a + p * b` with `a < p`. -/
lemma add_mul_eq_iff {p : ℕ} {a b a' b' : ℕ} (ha : a < p) (ha' : a' < p) :
    a + p * b = a' + p * b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have hmod : a = a' := by
      have h' := congrArg (fun x => x % p) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h'
      exact h'
    refine ⟨hmod, ?_⟩
    have hbb : p * b = p * b' := by
      rw [← hmod] at h
      exact Nat.add_left_cancel h
    exact Nat.mul_left_cancel (Nat.lt_of_le_of_lt (Nat.zero_le a) ha) hbb
  · rintro ⟨rfl, rfl⟩; rfl

/-- Splitting off the lowest digit from the "all digits are `p-1`" condition. -/
lemma conj_digits_iff (p c l : ℕ) :
    (c % p = p - 1 ∧ ∀ j, j < l → (c / p) / p ^ j % p = p - 1) ↔
    (∀ j, j < l + 1 → c / p ^ j % p = p - 1) := by
  constructor
  · rintro ⟨h0, h⟩ j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using h0
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
      rw [div_pow_succ p c k]
      exact h k (Nat.succ_lt_succ_iff.mp hj)
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h 0 (Nat.succ_pos l)
    · intro j hj
      rw [← div_pow_succ p c j]
      exact h (j + 1) (Nat.succ_lt_succ hj)

/-- The lowest `l` base-`p` digits of `c` are all equal to `p - 1` if and only if
`c % p ^ l = p ^ l - 1`. -/
theorem mod_pow_eq_pred_iff (p l c : ℕ) (hp : 1 ≤ p) :
    c % p ^ l = p ^ l - 1 ↔ ∀ j, j < l → c / p ^ j % p = p - 1 := by
  induction l generalizing c with
  | zero =>
    constructor
    · intro _ j hj; omega
    · intro _; simpa using Nat.mod_one c
  | succ l ih =>
    have step1 : (c % p ^ (l + 1) = p ^ (l + 1) - 1) ↔
        (c % p = p - 1 ∧ c / p % p ^ l = p ^ l - 1) := by
      rw [mod_pow_succ_eq p l c, ← pred_add_mul_pred p l hp]
      exact add_mul_eq_iff (Nat.mod_lt c (by omega)) (by omega)
    have step2 : (c % p = p - 1 ∧ c / p % p ^ l = p ^ l - 1) ↔
        (c % p = p - 1 ∧ ∀ j, j < l → (c / p) / p ^ j % p = p - 1) :=
      and_congr Iff.rfl (ih (c / p))
    exact step1.trans (step2.trans (conj_digits_iff p c l))

end Commons.Data.Nat