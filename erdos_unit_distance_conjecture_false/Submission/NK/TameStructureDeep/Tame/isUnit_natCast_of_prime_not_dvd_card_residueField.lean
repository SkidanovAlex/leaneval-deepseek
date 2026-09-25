import Mathlib

namespace NK.TameStructureDeep.Tame

/-- If `ℓ` is a prime and does not divide the cardinality of the (finite) residue
field of a local ring `R`, then `ℓ` is a unit in `R`.

Indeed, if `ℓ` were not a unit then its residue in `k = ResidueField R` would be
zero, so `1 ∈ k` would have additive order `ℓ`, whence `ℓ ∣ Nat.card k` by
Lagrange — contradicting the hypothesis. -/
theorem isUnit_natCast_of_prime_not_dvd_card_residueField {R : Type*} [CommRing R] [IsLocalRing R]
    [Finite (IsLocalRing.ResidueField R)] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ¬ ℓ ∣ Nat.card (IsLocalRing.ResidueField R)) : IsUnit (ℓ : R) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro hzero
  -- `ℓ` maps to `0` in the residue field
  have hcast : (ℓ : IsLocalRing.ResidueField R) = 0 := by
    simpa using hzero
  -- hence the additive order of `1` divides `ℓ`
  have hdvd : addOrderOf (1 : IsLocalRing.ResidueField R) ∣ ℓ := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    simpa [Nat.smul_one_eq_cast] using hcast
  -- and it is not `1` because the residue field is nontrivial
  have hne1 : addOrderOf (1 : IsLocalRing.ResidueField R) ≠ 1 := by
    intro h1
    rw [AddMonoid.addOrderOf_eq_one_iff] at h1
    exact one_ne_zero h1
  -- so, `ℓ` being prime, it must equal `ℓ`
  have heq : addOrderOf (1 : IsLocalRing.ResidueField R) = ℓ := by
    rcases hℓ.eq_one_or_self_of_dvd (addOrderOf (1 : IsLocalRing.ResidueField R)) hdvd with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  -- Lagrange: the order of `1` divides the cardinality of the residue field
  have := addOrderOf_dvd_natCard (1 : IsLocalRing.ResidueField R)
  rw [heq] at this
  exact h this

end NK.TameStructureDeep.Tame
