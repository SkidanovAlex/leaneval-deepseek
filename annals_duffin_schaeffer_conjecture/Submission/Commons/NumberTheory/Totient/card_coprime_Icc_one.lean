import Mathlib.Data.Nat.Totient

/-!
# Coprime counts in `Icc 1 q` equal the totient

`φ q` counts the naturals `< q` coprime to `q`; we prove the equivalent
characterisation counting the naturals `1 ≤ x ≤ q` coprime to `q`.
-/

namespace Commons.NumberTheory.Totient

open scoped Nat Finset

/-- The number of `1 ≤ x ≤ q` coprime to `q` equals the totient `φ q`. -/
theorem card_coprime_Icc_one (q : ℕ) : #{x ∈ Finset.Icc 1 q | q.Coprime x} = φ q := by
  have hset : Finset.Icc 1 q = Finset.Ico 1 (1 + q) := by
    ext x
    simp [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset]
  exact Nat.filter_coprime_Ico_eq_totient q 1

end Commons.NumberTheory.Totient
