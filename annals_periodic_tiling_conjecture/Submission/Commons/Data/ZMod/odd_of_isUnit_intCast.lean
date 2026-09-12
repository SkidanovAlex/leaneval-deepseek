import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int.Parity

namespace Commons.Data.ZMod

/-- An integer which is a unit modulo a power of two (of exponent at least one) is odd. -/
theorem odd_of_isUnit_intCast {t : ℕ} (ht : 1 ≤ t) {a : ℤ} (ha : IsUnit (a : ZMod (2 ^ t))) : Odd a := by
  have h2dvd : (2 : ℕ) ∣ 2 ^ t := by
    refine ⟨2 ^ (t - 1), ?_⟩
    rw [Nat.mul_comm, ← pow_succ, Nat.sub_add_cancel ht]
  -- Reduction modulo 2 maps units to units.
  have hza : IsUnit (a : ZMod 2) := by
    simpa using (RingHom.isUnit_map (ZMod.castHom h2dvd (ZMod 2)) ha)
  -- In `ZMod 2` the residue of an integer equals that of its absolute value.
  have hza' : IsUnit ((a.natAbs : ℕ) : ZMod 2) := by
    simpa [ZMod.natAbs_mod_two] using hza
  have hcop : (a.natAbs).Coprime 2 := (ZMod.isUnit_iff_coprime a.natAbs 2).1 hza'
  have hnot2 : ¬ 2 ∣ a.natAbs := by
    exact (Nat.prime_two.coprime_iff_not_dvd).1 (Nat.coprime_comm.mp hcop)
  have hoddAbs : Odd a.natAbs := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact hnot2 (even_iff_two_dvd.mp he)
  exact Int.natAbs_odd.mp hoddAbs

end Commons.Data.ZMod
