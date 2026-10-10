import Mathlib.Data.Nat.Factorization.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

/-- If `m` does not divide a nonzero `A`, then some prime `ℓ` has the full `ℓ`-part
`ℓ ^ (m.factorization ℓ)` of `m` not dividing `A`. -/
theorem exists_prime_pow_not_dvd_of_not_dvd {m A : ℕ} (hm : m ≠ 0) (hA : A ≠ 0) (h : ¬ m ∣ A) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ (ℓ ^ (m.factorization ℓ)) ∣ A := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  apply h
  rw [← Nat.factorization_le_iff_dvd hm hA, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · exact (Nat.Prime.pow_dvd_iff_le_factorization hp hA).mp (hc p hp)
  · rw [Nat.factorization_eq_zero_of_not_prime m hp]
    exact Nat.zero_le _

end NK.TameStructureDeep.Tame
