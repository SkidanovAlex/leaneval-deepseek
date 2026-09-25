import Mathlib
import Submission.NK.Chebotarev.ExistsSqrtInCyclotomic

/-!
# Square roots of rationals in `ℚ(ζ_N)`, with the level prescribed by the primes

`NK.Chebotarev.ExistsSqrtInCyclotomic` produces, for every rational `d`, *some* cyclotomic field
`ℚ(ζ_n)` containing a square root of `d`.  Here we prove the sharper statement needed by the
Čebotarev chapter: if `8 ∣ N` and the only primes occurring in `d = d.num / d.den` are primes that
divide `N`, then `ℚ(ζ_N)` itself already contains a square root of `d`.

The reason is the classical one.  Writing `m = d.num * d.den`, we have `d = m / d.den ^ 2`, so it
suffices to find a square root of the integer `m` in `ℚ(ζ_N)`.  Every prime `p ∣ m` divides `N` by
hypothesis, hence

* `p = 2`: `√2 = ζ_8 + ζ_8^{-1} ∈ ℚ(ζ_8) ⊆ ℚ(ζ_N)` (`exists_sq_eq_two_in_cyclotomic`),
* `p` odd: `ℚ(ζ_N)` contains the primitive `p`-th root of unity `ζ_N ^ (N/p)` and, since `4 ∣ N`,
  a square root `i` of `-1`, so the quadratic Gauss sum produces `√(±p)` and hence `√p`
  (`ExistsSqEqPrimeOfPrimitiveRoot`); a finite product of squares is a square
  (`ExistsSqEqNatCastOfPrimeSqrt`),
* the sign is harmless because `i` is available.
-/

set_option linter.style.haveILetI false

namespace NK.Chebotarev

/-- **If `8 ∣ N` and every prime dividing `d.num * d.den` divides `N`, then `d` is a square in
`ℚ(ζ_N)`.** -/
theorem exists_sq_eq_ratCast_in_cyclotomic_of_dvd (N : ℕ) [NeZero N] (h8 : 8 ∣ N) (d : ℚ)
    (hdiv : ∀ p : ℕ, Nat.Prime p → p ∣ (d.num * (d.den : ℤ)).natAbs → p ∣ N) :
    ∃ x : CyclotomicField N ℚ, x ^ 2 = algebraMap ℚ (CyclotomicField N ℚ) d := by
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  obtain ⟨ω, hω⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField N ℚ)
    (Set.mem_singleton N) (NeZero.ne N)
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one_in_cyclotomic N h8
  obtain ⟨s, hs⟩ := exists_sq_eq_two_in_cyclotomic N h8
  set m : ℤ := d.num * (d.den : ℤ) with hm
  -- every prime dividing `m` has a square root in `ℚ(ζ_N)`
  have hprime : ∀ p : ℕ, Nat.Prime p → p ∣ m.natAbs →
      ∃ x : CyclotomicField N ℚ, x ^ 2 = (p : CyclotomicField N ℚ) := by
    intro p hp hpdiv
    have hpN : p ∣ N := hdiv p hp (hm ▸ hpdiv)
    rcases eq_or_ne p 2 with rfl | hp2
    · exact ⟨s, by simpa using hs⟩
    · haveI : Fact p.Prime := ⟨hp⟩
      have hζ : IsPrimitiveRoot (ω ^ (N / p)) p :=
        isPrimitiveRoot_pow_div hω (NeZero.ne N) hp.ne_zero hpN
      exact ExistsSqEqPrimeOfPrimitiveRoot p hp2 hζ hi
  obtain ⟨y, hy⟩ := ExistsSqEqNatCastOfPrimeSqrt m.natAbs hprime
  have hdenQ : (d.den : ℚ) ≠ 0 := by exact_mod_cast d.pos.ne'
  -- `d = m / d.den ^ 2`
  have hd2 : d = (m : ℚ) / (d.den : ℚ) ^ 2 := by
    have hA : (m : ℚ) / (d.den : ℚ) ^ 2 = (d.num : ℚ) / (d.den : ℚ) := by
      have h1 : (m : ℚ) = (d.num : ℚ) * (d.den : ℚ) := by rw [hm]; push_cast; ring
      rw [h1, sq]
      field_simp
    rw [hA, Rat.num_div_den d]
  -- a square root of the integer `m` in `ℚ(ζ_N)`, handling the sign with `√(-1)`
  have hm_sqrt : ∃ z : CyclotomicField N ℚ, z ^ 2 = (m : CyclotomicField N ℚ) := by
    rcases lt_trichotomy m 0 with hneg | hzer | hpos
    · refine ⟨y * i, ?_⟩
      have hZ : -((m.natAbs : ℤ)) = m := by omega
      have key : (m : CyclotomicField N ℚ)
          = ((-((m.natAbs : ℤ)) : ℤ) : CyclotomicField N ℚ) :=
        congrArg (fun z : ℤ => (z : CyclotomicField N ℚ)) hZ.symm
      have hcast : (m : CyclotomicField N ℚ)
          = -((m.natAbs : ℕ) : CyclotomicField N ℚ) := by
        rw [key, Int.cast_neg, Int.cast_natCast]
      rw [hcast, mul_pow, hy, hi]
      ring
    · refine ⟨0, ?_⟩
      rw [hzer]; simp
    · refine ⟨y, ?_⟩
      have hnm : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_lt hpos)
      have key : (((m.natAbs : ℤ)) : CyclotomicField N ℚ)
          = (m : CyclotomicField N ℚ) :=
        congrArg (fun z : ℤ => (z : CyclotomicField N ℚ)) hnm
      have hcast : ((m.natAbs : ℕ) : CyclotomicField N ℚ)
          = (m : CyclotomicField N ℚ) := by
        rw [← Int.cast_natCast, key]
      rw [hy, hcast]
  obtain ⟨z, hz⟩ := hm_sqrt
  -- `√d = √m / d.den`
  refine ⟨z / (d.den : CyclotomicField N ℚ), ?_⟩
  have hcast2 : (m : CyclotomicField N ℚ) / (d.den : CyclotomicField N ℚ) ^ 2
      = algebraMap ℚ (CyclotomicField N ℚ) ((m : ℚ) / (d.den : ℚ) ^ 2) := by
    rw [map_div₀, map_pow, map_natCast, map_intCast]
  rw [div_pow, hz, hcast2]
  exact congrArg (algebraMap ℚ (CyclotomicField N ℚ)) hd2.symm

end NK.Chebotarev
