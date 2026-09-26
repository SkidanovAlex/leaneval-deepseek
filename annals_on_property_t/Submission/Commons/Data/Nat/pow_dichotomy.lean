import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic

set_option linter.unusedVariables false
namespace Commons.Data.Nat

/-- Digit-block comparison in an arbitrary base `B`: if the low digits `y` and `v`
are both `< B`, then `B * x + y < B * u + v` holds exactly when the high digits
compare (`x < u`), or are equal and the low digits compare (`y < v`).

This is the arithmetic heart of comparing two length-`2` positional encodings. -/
lemma mul_add_lt_mul_add_iff {B x y u v : ℕ} (hy : y < B) (hv : v < B) :
    B * x + y < B * u + v ↔ x < u ∨ (x = u ∧ y < v) := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy x u with hxu | hxu | hxu
    · exact Or.inl hxu
    · subst hxu
      exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      have h1 : B * (u + 1) ≤ B * x :=
        Nat.mul_le_mul_left B (Nat.succ_le_of_lt hxu)
      rw [Nat.mul_succ] at h1
      omega
  · rintro (hxu | ⟨hxu, hyv⟩)
    · have h1 : B * (x + 1) ≤ B * u :=
        Nat.mul_le_mul_left B (Nat.succ_le_of_lt hxu)
      rw [Nat.mul_succ] at h1
      omega
    · subst hxu
      omega

/-- Pure arithmetic dichotomy for the balanced-side energy step.

For `C ≥ 2`, `k ≤ p`, `k ≤ q`, all four numbers `a, a', b, b'` below `C^k`, and
excluding the degenerate case `a = b' ∧ b = a'`, at least one of the two
inequalities holds. -/
theorem pow_dichotomy {C k p q a a' b b' : ℕ} (hC : 2 ≤ C) (hkp : k ≤ p) (hkq : k ≤ q)
    (ha : a < C ^ k) (ha' : a' < C ^ k) (hb : b < C ^ k) (hb' : b' < C ^ k)
    (hnd : ¬ (a = b' ∧ b = a')) :
    b + C ^ p * b' < C ^ p * a + a' ∨ C ^ q * a + a' < C ^ q * b' + b := by
  have hCpos : 0 < C := by omega
  have hkp' : C ^ k ≤ C ^ p := Nat.pow_le_pow_right hCpos hkp
  have hkq' : C ^ k ≤ C ^ q := Nat.pow_le_pow_right hCpos hkq
  have hbp : b < C ^ p := lt_of_lt_of_le hb hkp'
  have ha'p : a' < C ^ p := lt_of_lt_of_le ha' hkp'
  have hbq : b < C ^ q := lt_of_lt_of_le hb hkq'
  have ha'q : a' < C ^ q := lt_of_lt_of_le ha' hkq'
  -- First inequality, read in base `C^p`.
  have key1 : (b + C ^ p * b' < C ^ p * a + a') ↔ b' < a ∨ (b' = a ∧ b < a') := by
    rw [Nat.add_comm b (C ^ p * b')]
    exact mul_add_lt_mul_add_iff hbp ha'p
  -- Second inequality, read in base `C^q` (with the two sides swapped).
  have key2 : (C ^ q * a + a' < C ^ q * b' + b) ↔ a < b' ∨ (a = b' ∧ a' < b) :=
    mul_add_lt_mul_add_iff ha'q hbq
  rcases Nat.lt_trichotomy b' a with h | h | h
  · exact Or.inl (key1.mpr (Or.inl h))
  · have hneq : b ≠ a' := fun hh => hnd ⟨h.symm, hh⟩
    rcases Nat.lt_trichotomy b a' with h2 | h2 | h2
    · exact Or.inl (key1.mpr (Or.inr ⟨h, h2⟩))
    · exact absurd h2 hneq
    · exact Or.inr (key2.mpr (Or.inr ⟨h.symm, h2⟩))
  · exact Or.inr (key2.mpr (Or.inl h))

end Commons.Data.Nat