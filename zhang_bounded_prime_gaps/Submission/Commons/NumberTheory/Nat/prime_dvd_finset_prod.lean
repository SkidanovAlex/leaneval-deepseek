import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Prime.Defs

namespace Commons.NumberTheory.Nat

theorem prime_dvd_finset_prod {ι : Type*} (s : Finset ι) {q : ℕ} (hq : Nat.Prime q) (f : ι → ℕ) :
    q ∣ ∏ x ∈ s, f x → ∃ x ∈ s, q ∣ f x := by
  intro h
  rw [show (∏ x ∈ s, f x) = s.prod f by rfl] at h
  exact (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hq) f).mp h

end Commons.NumberTheory.Nat