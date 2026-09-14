import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial

namespace Commons.NumberTheory.NumberField

theorem minpoly_nextCoeff_eq_zero_of_trace_eq_zero {K : Type*} [Field K] [NumberField K]
    (x : NumberField.RingOfIntegers K)
    (h : Algebra.trace ℚ K ((x : NumberField.RingOfIntegers K) : K) = 0) :
    (minpoly ℤ x).nextCoeff = 0 := by
  have hint : IsIntegral ℤ x := IsIntegralClosure.isIntegral ℤ K x
  have hmap : minpoly ℚ ((x : NumberField.RingOfIntegers K) : K)
      = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ K hint
  have hnext : (minpoly ℚ ((x : NumberField.RingOfIntegers K) : K)).nextCoeff = 0 := by
    have htr := trace_eq_finrank_mul_minpoly_nextCoeff ℚ ((x : NumberField.RingOfIntegers K) : K)
    rw [h] at htr
    have hfd : ((Module.finrank (IntermediateField.adjoin ℚ {((x : NumberField.RingOfIntegers K) : K)}) K : ℕ) : ℚ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Module.finrank_pos.ne'
    rcases mul_eq_zero.mp htr.symm with h1 | h2
    · exact absurd h1 hfd
    · exact neg_eq_zero.mp h2
  have hcoe : (algebraMap ℤ ℚ) ((minpoly ℤ x).nextCoeff) = 0 := by
    rw [← Polynomial.nextCoeff_map (FaithfulSMul.algebraMap_injective ℤ ℚ) (minpoly ℤ x), ← hmap]
    exact hnext
  exact FaithfulSMul.algebraMap_injective ℤ ℚ (by rw [hcoe, map_zero])

end Commons.NumberTheory.NumberField