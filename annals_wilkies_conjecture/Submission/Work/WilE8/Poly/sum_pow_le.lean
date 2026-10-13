import Mathlib

namespace Work.WilE8.Poly

/-- For a nonzero exponent `e`, the sum of the `e`-th powers of the values of `D` over a
finite set `s` is at most the `e`-th power of the sum. -/
lemma finset_sum_pow_le {α : Type*} (e : ℕ) (he : e ≠ 0) (D : α → ℕ) (s : Finset α) :
    ∑ i ∈ s, D i ^ e ≤ (∑ i ∈ s, D i) ^ e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_pow he]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc D a ^ e + ∑ i ∈ s, D i ^ e
        ≤ D a ^ e + (∑ i ∈ s, D i) ^ e := add_le_add (le_refl _) ih
      _ ≤ (D a + ∑ i ∈ s, D i) ^ e :=
          pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) he

theorem sum_pow_le {k : ℕ} (e : ℕ) (he : 1 ≤ e) (D : Fin k → ℕ) :
    ∑ i, D i ^ e ≤ (∑ i, D i) ^ e := by
  classical
  simpa using
    finset_sum_pow_le e (Nat.one_le_iff_ne_zero.mp he) D (Finset.univ : Finset (Fin k))

end Work.WilE8.Poly
