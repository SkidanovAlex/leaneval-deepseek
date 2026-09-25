import Mathlib.GroupTheory.OrderOfElement

namespace Commons.GroupTheory

/-- If a group element has two coprime exponent-annihilating powers, it is the
identity: its order divides both `a` and `b`, hence their gcd `1`. -/
theorem pow_eq_one_of_coprime_exp {G : Type*} [Group G] (g : G) (a b : ℕ)
    (hga : g ^ a = 1) (hgb : g ^ b = 1) (hcop : Nat.Coprime a b) : g = 1 := by
  apply orderOf_eq_one_iff.mp
  have hda : orderOf g ∣ a := orderOf_dvd_iff_pow_eq_one.mpr hga
  have hdb : orderOf g ∣ b := orderOf_dvd_iff_pow_eq_one.mpr hgb
  have hd : orderOf g ∣ a.gcd b := Nat.dvd_gcd hda hdb
  have hg : a.gcd b = 1 := hcop.gcd_eq_one
  rwa [hg, Nat.dvd_one] at hd

end Commons.GroupTheory