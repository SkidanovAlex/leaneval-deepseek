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

set_option linter.style.haveILetI false

/-- In `GaloisField 2 (2 * n + 1)` the `(n + 1)`-fold Frobenius map `x ↦ x ^ (2 ^ (n + 1))`
is not the identity: this field has `2 ^ (2 * n + 1) > 2 ^ (n + 1)` elements, so not every
element can be a root of the degree-`2 ^ (n + 1)` polynomial `X ^ (2 ^ (n + 1)) - X`.

The proof uses the companion identity
`(x ^ 2 ^ (n + 1)) ^ 2 ^ (n + 1) = x ^ 2`: if every element were fixed by `x ↦ x ^ (2 ^ (n + 1))`,
then `x ^ 2 = x` for every `x`, so the field would contain at most the two idempotents `0` and
`1`, contradicting `Nat.card = 2 ^ (2 * n + 1) ≥ 8`. -/
theorem exists_pow_two_pow_ne_self (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : GaloisField 2 (2 * n + 1), x ^ (2 ^ (n + 1)) ≠ x := by
  haveI : Fintype (GaloisField 2 (2 * n + 1)) := Fintype.ofFinite _
  have hcardK : Fintype.card (GaloisField 2 (2 * n + 1)) = 2 ^ (2 * n + 1) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card]
    omega
  by_contra h
  simp only [not_exists, not_not] at h
  haveI := Classical.decEq (GaloisField 2 (2 * n + 1))
  -- If every element is fixed by the `(n + 1)`-fold Frobenius, then so is the squaring map.
  have hsq : ∀ x : GaloisField 2 (2 * n + 1), x ^ 2 = x := by
    intro x
    have hx := galoisField_pow_two_pow_succ_succ n x
    rw [h x, h x] at hx
    exact hx.symm
  -- Hence every element is idempotent, i.e. `0` or `1`.
  have hidem : ∀ x : GaloisField 2 (2 * n + 1), x = 0 ∨ x = 1 := by
    intro x
    have hx : x * (x - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_two, hsq x, sub_self]
    rcases mul_eq_zero.mp hx with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  -- So the whole field is contained in the two-element set `{0, 1}`.
  have hsub : (Finset.univ : Finset (GaloisField 2 (2 * n + 1))) ⊆ {0, 1} := by
    intro x _
    rcases hidem x with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  have hle : Fintype.card (GaloisField 2 (2 * n + 1)) ≤ 2 := by
    calc Fintype.card (GaloisField 2 (2 * n + 1))
        = (Finset.univ : Finset (GaloisField 2 (2 * n + 1))).card := Finset.card_univ.symm
      _ ≤ ({0, 1} : Finset (GaloisField 2 (2 * n + 1))).card := Finset.card_le_card hsub
      _ = 2 := Finset.card_pair zero_ne_one
  -- But the cardinality is `2 ^ (2 * n + 1) ≥ 2 ^ 3 = 8 > 2`, a contradiction.
  rw [hcardK] at hle
  have hge : 3 ≤ 2 * n + 1 := by omega
  have h8 : (2 : ℕ) ^ 3 ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) hge
  omega

end Commons.FieldTheory.FiniteField