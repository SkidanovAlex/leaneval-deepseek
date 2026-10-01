import Mathlib

namespace Work.LinnikBurgess

/-- Divisibility of the canonical representative.  For `g ≤ K`, a power `p^g` divides the
representative `(d : ZMod (p^K)).val = d mod p^K` if and only if it divides `d` itself. -/
theorem dvd_natCast_val_iff {p K g d : ℕ} [Fact p.Prime] (hg : g ≤ K) :
    (p ^ g ∣ (((d : ℕ) : ZMod (p ^ K))).val) ↔ (p ^ g ∣ d) := by
  rw [ZMod.val_natCast (p ^ K) d, Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  rw [Nat.ModEq.of_dvd (pow_dvd_pow p hg) (Nat.mod_modEq d (p ^ K))]

end Work.LinnikBurgess
