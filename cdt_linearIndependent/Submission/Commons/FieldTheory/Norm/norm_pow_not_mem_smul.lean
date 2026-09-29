import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Norm

open scoped BigOperators

/-- If a rational number is integral over `ℤ`, it is an integer. -/
lemma norm_pow_rat_isIntegral_isInt {q : ℚ} (hq : IsIntegral ℤ q) :
    ∃ z : ℤ, (z : ℚ) = q := by
  rcases (IsIntegral.exists_int_iff_exists_rat (α := ℚ) hq).1 ⟨q, rfl⟩ with ⟨z, hz⟩
  exact ⟨z, hz.symm⟩

/-- The norm of `m * x ^ p` (with `m` an integer scalar) in a finite
`ℚ`-algebra. -/
lemma norm_pow_norm_intCast_mul {L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (m : ℤ) (x : L) (p : ℕ) :
    Algebra.norm ℚ ((m : L) * x ^ p) =
      (m : ℚ) ^ Module.finrank ℚ L * (Algebra.norm ℚ x) ^ p := by
  rw [show (m : L) = algebraMap ℚ L (m : ℚ) from (map_intCast (algebraMap ℚ L) m).symm]
  rw [map_mul, map_pow, Algebra.norm_algebraMap]

/-- The norm of `p * w` (with `p : ℕ` a scalar) in a finite `ℚ`-algebra. -/
lemma norm_pow_norm_natCast_mul {L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (p : ℕ) (w : L) :
    Algebra.norm ℚ ((p : L) * w) =
      (p : ℚ) ^ Module.finrank ℚ L * (Algebra.norm ℚ w) := by
  rw [show (p : L) = algebraMap ℚ L (p : ℚ) from (map_natCast (algebraMap ℚ L) p).symm]
  rw [map_mul, Algebra.norm_algebraMap]

lemma norm_pow_not_mem_smul {L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] {δ : L} (hδ0 : δ ≠ 0) (hδint : IsIntegral ℤ δ)
    {m : ℤ} (hm : m ≠ 0) {p : ℕ} (hp : Nat.Prime p) {N : ℤ}
    (hN : (N : ℚ) = Algebra.norm ℚ δ) (hpd : ¬ (p : ℤ) ∣ m * N) :
    ¬ ∃ w : L, IsIntegral ℤ w ∧ (m : L) * δ ^ p = (p : L) * w := by
  rintro ⟨w, hwint, hw⟩
  have hnormw_int : IsIntegral ℤ (Algebra.norm ℚ w) := Algebra.isIntegral_norm ℚ hwint
  obtain ⟨z, hz⟩ := norm_pow_rat_isIntegral_isInt hnormw_int
  -- `hw : (m : L) * δ ^ p = (p : L) * w`; take norms on both sides.
  have hn : (m : ℚ) ^ Module.finrank ℚ L * (N : ℚ) ^ p =
      (p : ℚ) ^ Module.finrank ℚ L * (z : ℚ) := by
    have hn0 : Algebra.norm ℚ ((m : L) * δ ^ p) = Algebra.norm ℚ ((p : L) * w) := by
      rw [hw]
    rw [norm_pow_norm_intCast_mul, norm_pow_norm_natCast_mul] at hn0
    rw [← hN, ← hz] at hn0
    exact hn0
  -- Both sides are integers, so we obtain an equality in `ℤ`.
  have hIntEq : (m ^ Module.finrank ℚ L * N ^ p : ℤ) =
      (p : ℤ) ^ Module.finrank ℚ L * z := by
    exact_mod_cast hn
  -- Since `L` is a field extension of `ℚ`, its dimension is positive.
  have hdpos : 0 < Module.finrank ℚ L := Module.finrank_pos (R := ℚ) (M := L)
  have hprime : Prime (p : ℤ) := (Nat.prime_iff_prime_int).1 hp
  -- `p ∤ m` and `p ∤ N` follow from `p ∤ m * N` (primality of `p`).
  have hpm : ¬ (p : ℤ) ∣ m := by
    intro h
    exact hpd (dvd_mul_of_dvd_left h N)
  have hpn : ¬ (p : ℤ) ∣ N := by
    intro h
    exact hpd (dvd_mul_of_dvd_right h m)
  -- Hence `p ∤ m ^ [L:ℚ] * N ^ p`...
  have hpmd : ¬ (p : ℤ) ∣ m ^ Module.finrank ℚ L := by
    intro h
    exact hpm (Prime.dvd_of_dvd_pow hprime h)
  have hpnp : ¬ (p : ℤ) ∣ N ^ p := by
    intro h
    exact hpn (Prime.dvd_of_dvd_pow hprime h)
  have hdiv_not : ¬ (p : ℤ) ∣ m ^ Module.finrank ℚ L * N ^ p := by
    intro h
    rcases (Prime.dvd_mul hprime).1 h with h1 | h2
    · exact hpmd h1
    · exact hpnp h2
  -- ... while `p` divides the right-hand side `p ^ [L:ℚ] * z`.
  have hp_dvd : (p : ℤ) ∣ (p : ℤ) ^ Module.finrank ℚ L := by
    simpa using (pow_dvd_pow (p : ℤ) (Nat.succ_le_of_lt hdpos))
  have hdiv_yes : (p : ℤ) ∣ (p : ℤ) ^ Module.finrank ℚ L * z := by
    exact dvd_mul_of_dvd_left hp_dvd z
  have hcontra : (p : ℤ) ∣ m ^ Module.finrank ℚ L * N ^ p := by
    rw [hIntEq]
    exact hdiv_yes
  exact hdiv_not hcontra

end Commons.FieldTheory.Norm