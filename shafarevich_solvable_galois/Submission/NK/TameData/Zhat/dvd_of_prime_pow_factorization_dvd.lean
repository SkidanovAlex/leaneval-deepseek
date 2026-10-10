import Mathlib.Data.Nat.Factorization.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameData.Zhat

/-- If every prime power `ℓ ^ (m.factorization ℓ)` divides `n`, then `m` divides `n`.

Proof: for `n = 0` this is trivial.  Otherwise reduce to `ℕ` via `Int.natAbs`, where
`m = ∏ ℓ, ℓ ^ (m.factorization ℓ)`; it suffices to compare `p`-adic valuations. -/
theorem dvd_of_prime_pow_factorization_dvd {m : ℕ} (hm : m ≠ 0) {n : ℤ}
    (h : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ^ m.factorization ℓ ∣ n) : (m : ℤ) ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  have hn' : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have key : ∀ p : ℕ, p.Prime → m.factorization p ≤ n.natAbs.factorization p := by
    intro p hp
    have hpz : p ^ m.factorization p ∣ n.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr (h p hp)
      simpa [Int.natAbs_pow] using this
    exact (hp.pow_dvd_iff_le_factorization hn').mp hpz
  have hdvd : m ∣ n.natAbs := (Nat.factorization_prime_le_iff_dvd hm hn').mp key
  exact Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.mpr hdvd)

end NK.TameData.Zhat
