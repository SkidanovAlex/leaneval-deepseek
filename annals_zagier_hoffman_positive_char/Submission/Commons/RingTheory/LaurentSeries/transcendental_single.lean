import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.RingTheory.LaurentSeries

open Polynomial

/-- The `algebraMap` from a field into its Laurent series (Hahn series indexed by `ℤ`) sends a
scalar to the corresponding constant series. -/
lemma algebraMap_laurent_eq_single {F : Type*} [Field F] (a : F) :
    algebraMap F (LaurentSeries F) a = HahnSeries.single 0 a := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]
  simp [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

/-- A constant Laurent series multiplied by a power of the monomial `single d c` is again a
monomial. -/
lemma single_mul_pow_single {F : Type*} [Field F] {d : ℤ} {c : F} (k : ℕ) (a : F) :
    algebraMap F (LaurentSeries F) a * (HahnSeries.single d c) ^ k
      = HahnSeries.single ((k : ℤ) * d) (a * c ^ k) := by
  rw [algebraMap_laurent_eq_single, HahnSeries.single_pow,
      HahnSeries.single_mul_single, zero_add]
  congr 1

/-- The coefficient at the exponent `n * d` of `p(single d c)` reads off the `n`-th coefficient of
`p` (times `c ^ n`), when `d ≠ 0`. -/
lemma coeff_eval₂_single {F : Type*} [Field F] {d : ℤ} (hd : d ≠ 0) {c : F}
    (p : Polynomial F) (n : ℕ) :
    (Polynomial.eval₂ (algebraMap F (LaurentSeries F)) (HahnSeries.single d c) p).coeff
        ((n : ℤ) * d)
      = p.coeff n * c ^ n := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, HahnSeries.coeff_sum]
  have hterm : ∀ i : ℕ,
      ((algebraMap F (LaurentSeries F)) (p.coeff i) * (HahnSeries.single d) c ^ i).coeff
          ((n : ℤ) * d)
        = if i = n then p.coeff i * c ^ i else 0 := by
    intro i
    rw [single_mul_pow_single (d := d) (c := c) i (p.coeff i), HahnSeries.coeff_single]
    by_cases hin : i = n
    · subst hin; simp
    · rw [if_neg hin, if_neg]
      intro h
      exact hin (by
        have h' : (i : ℤ) = (n : ℤ) := (mul_right_cancel₀ hd h).symm
        exact_mod_cast h')
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_ite_eq']
  by_cases hn : n ∈ p.support
  · rw [if_pos hn]
  · rw [if_neg hn]
    have hc0 : p.coeff n = 0 := by
      by_contra hne
      exact hn ((Polynomial.mem_support_iff).mpr hne)
    rw [hc0, zero_mul]

theorem transcendental_single {F : Type*} [Field F] {d : ℤ} {c : F} (hd : d ≠ 0) (hc : c ≠ 0) :
    ∀ p : Polynomial F, Polynomial.eval₂ (algebraMap F (LaurentSeries F)) (HahnSeries.single d c) p = 0 → p = 0 := by
  intro p hp
  rw [Polynomial.ext_iff]
  intro n
  have h := congrArg (fun x : LaurentSeries F => x.coeff ((n : ℤ) * d)) hp
  rw [HahnSeries.coeff_zero, coeff_eval₂_single (F := F) hd p n] at h
  exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero n hc)

end Commons.RingTheory.LaurentSeries