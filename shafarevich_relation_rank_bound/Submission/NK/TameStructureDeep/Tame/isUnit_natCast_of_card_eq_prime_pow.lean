import Mathlib

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Tame

/-- In a local ring whose residue field has cardinality `p ^ e` with `p` prime, every prime
`ℓ ≠ p` is a unit. -/
theorem isUnit_natCast_of_card_eq_prime_pow {A : Type*} [CommRing A] [IsLocalRing A]
    [Finite (IsLocalRing.ResidueField A)] {p e : ℕ} (hp : p.Prime)
    (hcard : Nat.card (IsLocalRing.ResidueField A) = p ^ e) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓp : ℓ ≠ p) : IsUnit (ℓ : A) := by
  haveI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  obtain ⟨r, hCharP, n, hrn, hncard⟩ := FiniteField.card' (IsLocalRing.ResidueField A)
  haveI : CharP (IsLocalRing.ResidueField A) r := hCharP
  have hcardK : Fintype.card (IsLocalRing.ResidueField A) = p ^ e := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have heq : r ^ (n : ℕ) = p ^ e := by rw [← hncard, hcardK]
  have hdvd : r ∣ p ^ e := heq ▸ dvd_pow_self r n.ne_zero
  have hdvd_p : r ∣ p := hrn.dvd_of_dvd_pow hdvd
  have hrp : r = p := by
    rcases (Nat.dvd_prime hp).mp hdvd_p with h1 | h1
    · exact absurd h1 hrn.ne_one
    · exact h1
  have hne : ((ℓ : IsLocalRing.ResidueField A)) ≠ 0 := by
    intro h
    have hd : r ∣ ℓ := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) r ℓ).mp h
    rw [hrp] at hd
    rcases (Nat.dvd_prime hℓ).mp hd with h1 | h1
    · exact hp.ne_one h1
    · exact hℓp h1.symm
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit (ℓ : A)]
  rw [map_natCast (IsLocalRing.residue A) ℓ]
  exact hne

end NK.TameStructureDeep.Tame
