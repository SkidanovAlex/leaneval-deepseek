import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Data.Nat.Prime.Int

/-!
# Eisenstein's criterion at 2 over ℤ

The final assembly constructs monic integer polynomials whose non-leading
coefficients are all even and whose constant term is not divisible by 4;
Eisenstein at the prime ideal `(2)` makes them irreducible over ℤ.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Submission.EisensteinInt

/-- Eisenstein at 2: a monic integer polynomial of positive degree, all of
whose non-leading coefficients are even and whose constant coefficient is not
divisible by 4, is irreducible over ℤ. -/
theorem irreducible_of_eisenstein_two {F : Polynomial ℤ} (hdeg : 0 < F.natDegree)
    (hmon : F.Monic) (heven : ∀ k : ℕ, k < F.natDegree → Even (F.coeff k))
    (hnd4 : ¬ (4 : ℤ) ∣ F.coeff 0) : Irreducible F := by
  let 𝓟 : Ideal ℤ := Ideal.span ({2} : Set ℤ)
  have hprime : 𝓟.IsPrime := by
    have hpr2 : Prime (2 : ℤ) := by
      change Prime (((2 : ℕ) : ℤ))
      exact (Nat.prime_iff_prime_int (p := 2)).mp Nat.prime_two
    exact (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr hpr2
  have hmem2 : ∀ {k : ℕ}, k < F.natDegree → F.coeff k ∈ 𝓟 := by
    intro k hk
    have hev : Even (F.coeff k) := heven k hk
    rw [Ideal.mem_span_singleton]
    exact even_iff_two_dvd.mp hev
  have hnotMem : F.coeff 0 ∉ 𝓟 ^ 2 := by
    intro h
    have hsq : (Ideal.span ({2} : Set ℤ)) ^ 2 = Ideal.span ({(2 : ℤ) ^ 2} : Set ℤ) := by
      exact Ideal.span_singleton_pow (2 : ℤ) 2
    rw [hsq, Ideal.mem_span_singleton] at h
    norm_num at h
    exact hnd4 h
  have hIsEis : F.IsEisensteinAt 𝓟 := by
    refine ⟨?leading, ?mem, ?notMem⟩
    · have hlc : F.leadingCoeff = 1 := hmon.leadingCoeff
      rw [hlc]
      intro h1
      rw [Ideal.mem_span_singleton] at h1
      norm_num at h1
    · exact fun {n} hn => hmem2 hn
    · exact hnotMem
  exact hIsEis.irreducible hprime hmon.isPrimitive hdeg

end Submission.EisensteinInt
