/-
# Uniqueness of the binary representation of a sum of two powers of two

`2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d` with `a ≤ b`, `c ≤ d` forces `a = c` and `b = d`.
This is the arithmetic input for the coefficient comparison in App. VIII Prop. 3.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.Hering.AppVIII

/-- The `2`-adic valuation of `2 ^ a + 2 ^ b` for `a < b` is `a`. -/
theorem factorization_twoPow_add_of_lt {a b : ℕ} (hab : a < b) :
    (2 ^ a + 2 ^ b).factorization 2 = a := by
  have hb : 2 ^ b = 2 ^ a * 2 ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hab)]
  have hk : 1 ≤ b - a := Nat.sub_pos_of_lt hab
  have hodd : Odd (1 + 2 ^ (b - a)) := by
    obtain ⟨k, hk'⟩ : ∃ k, b - a = k + 1 := ⟨b - a - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
    refine ⟨2 ^ k, ?_⟩
    rw [hk', pow_succ]
    ring
  have ha0 : (2 : ℕ) ^ a ≠ 0 := (Nat.two_pow_pos a).ne'
  have hb0 : 1 + 2 ^ (b - a) ≠ 0 := by positivity
  have hmul : 2 ^ a + 2 ^ b = 2 ^ a * (1 + 2 ^ (b - a)) := by
    rw [hb, mul_add, mul_one]
  rw [hmul, Nat.factorization_mul ha0 hb0]
  simp only [Finsupp.add_apply]
  rw [Nat.factorization_pow_self Nat.prime_two]
  have hz : (1 + 2 ^ (b - a)).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    obtain ⟨k, hk'⟩ := hodd
    obtain ⟨m, hm⟩ := hdvd
    omega
  rw [hz, add_zero]

/-- The `2`-adic valuation of `2 ^ a + 2 ^ a` is `a + 1`. -/
theorem factorization_twoPow_add_self (a : ℕ) :
    (2 ^ a + 2 ^ a).factorization 2 = a + 1 := by
  have h : 2 ^ a + 2 ^ a = 2 ^ (a + 1) := by rw [pow_succ]; ring
  rw [h, Nat.factorization_pow_self Nat.prime_two]

/-- **Uniqueness of the binary representation.** If `2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d` with
`a ≤ b` and `c ≤ d`, then `a = c` and `b = d`. -/
theorem twoPowAddEq {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) : a = c ∧ b = d := by
  have hinj : Function.Injective fun n : ℕ => (2 : ℕ) ^ n := Nat.pow_right_injective (by norm_num)
  have hfac : (2 ^ a + 2 ^ b).factorization 2 = (2 ^ c + 2 ^ d).factorization 2 := by rw [h]
  rcases lt_trichotomy a b with hab' | hab' | hab'
  · rcases lt_trichotomy c d with hcd' | hcd' | hcd'
    · -- `a < b`, `c < d`: both valuations are `a` resp. `c`
      have hac : a = c := by
        rw [factorization_twoPow_add_of_lt hab', factorization_twoPow_add_of_lt hcd'] at hfac
        exact hfac
      subst hac
      refine ⟨rfl, hinj ?_⟩
      exact Nat.add_left_cancel (show 2 ^ a + 2 ^ b = 2 ^ a + 2 ^ d from h)
    · -- `a < b`, `c = d`: valuation of `2 ^ c + 2 ^ d` is `c + 1`, absurd
      exfalso
      rw [factorization_twoPow_add_of_lt hab', hcd', factorization_twoPow_add_self] at hfac
      have hh : 2 ^ c + 2 ^ d = 2 ^ a := by
        calc 2 ^ c + 2 ^ d = 2 ^ d + 2 ^ d := by rw [hcd']
          _ = 2 ^ (d + 1) := by rw [pow_succ]; ring
          _ = 2 ^ a := by rw [← hfac]
      have h4 : 2 ^ a + 2 ^ b = 2 ^ a + 0 := by rw [h, hh, add_zero]
      exact absurd (Nat.add_left_cancel h4) (Nat.two_pow_pos b).ne'
    · exact absurd hcd (not_le_of_gt hcd')
  · rcases lt_trichotomy c d with hcd' | hcd' | hcd'
    · -- `a = b`, `c < d`
      exfalso
      rw [hab', factorization_twoPow_add_self, factorization_twoPow_add_of_lt hcd'] at hfac
      -- `hfac : b + 1 = c`
      have hh : 2 ^ c = 2 ^ b + 2 ^ b := by
        calc 2 ^ c = 2 ^ (b + 1) := by rw [hfac]
          _ = 2 ^ b + 2 ^ b := by rw [pow_succ]; ring
      have h5 : 2 ^ b + 2 ^ b = (2 ^ b + 2 ^ b) + 2 ^ d := by
        calc 2 ^ b + 2 ^ b = 2 ^ a + 2 ^ b := by rw [hab']
          _ = 2 ^ c + 2 ^ d := h
          _ = (2 ^ b + 2 ^ b) + 2 ^ d := by rw [hh]
      have h6 : (2 ^ b + 2 ^ b) + 2 ^ d = (2 ^ b + 2 ^ b) + 0 := by
        rw [add_zero, ← h5]
      exact absurd (Nat.add_left_cancel h6) (Nat.two_pow_pos d).ne'
    · -- `a = b`, `c = d`: both valuations are `+ 1`
      rw [hab', factorization_twoPow_add_self, hcd', factorization_twoPow_add_self] at hfac
      exact ⟨by omega, by omega⟩
    · exact absurd hcd (not_le_of_gt hcd')
  · exact absurd hab (not_le_of_gt hab')

/-- Unordered form: `2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d` forces `{a, b} = {c, d}`. -/
theorem twoPowAddEq' {a b c d : ℕ} (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases le_total a b with hab | hab
  · rcases le_total c d with hcd | hcd
    · exact Or.inl (twoPowAddEq hab hcd h)
    · refine Or.inr (twoPowAddEq (a := a) (b := b) (c := d) (d := c) hab hcd ?_)
      rw [h, add_comm]
  · rcases le_total c d with hcd | hcd
    · have h' : 2 ^ b + 2 ^ a = 2 ^ c + 2 ^ d := by rw [add_comm, h]
      obtain ⟨h1, h2⟩ := twoPowAddEq (a := b) (b := a) (c := c) (d := d) hab hcd h'
      exact Or.inr ⟨h2, h1⟩
    · have h' : 2 ^ b + 2 ^ a = 2 ^ d + 2 ^ c := by rw [add_comm, h, add_comm]
      obtain ⟨h1, h2⟩ := twoPowAddEq (a := b) (b := a) (c := d) (d := c) hab hcd h'
      exact Or.inl ⟨h2, h1⟩

end Work.Hering.AppVIII
