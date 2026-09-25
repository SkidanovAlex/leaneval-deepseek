import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_integral

/-!
# The Artin symbol of a principal ideal `(a)` with `a ≡ 1 mod m` and `a` totally positive,
from the ideal-theoretic reciprocity law

This is the same statement as `NK.CFTLib.Arl.artinSym_spanSingleton_integral`, except that the
hypothesis `a ≠ 0` is replaced by the (weaker, hypothesis-level) congruence condition
`a - 1 ∈ (m)` together with `0 < m`.  The two differ only in the degenerate case `a = 0`,
which can occur only when `m` is a unit of `𝓞 K` (in particular `m = 1`); there
`spanSingleton 𝓞⁰ (0 : K) = 0` and the Artin symbol is trivially `1`.

## Main result

* `NK.CFTLib.Arl.artinSym_spanSingleton_integral_of_hprinc`
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The exponent vector of the zero fractional ideal is zero. -/
lemma exps_zero : exps (0 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
  ext 𝔭
  rw [exps_apply, FractionalIdeal.count_zero, Finsupp.zero_apply]

/-- The Artin symbol of the zero fractional ideal is trivial. -/
lemma artinSym_zero (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    artinSym (K := K) (L := L) hcomm (0 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1 := by
  letI := galCommMonoid hcomm
  unfold artinSym
  rw [exps_zero]
  exact Finsupp.prod_zero_index

theorem artinSym_spanSingleton_integral_of_hprinc {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : ∀ (a : NumberField.RingOfIntegers K),
      a - 1 ∈ Ideal.span {(m : NumberField.RingOfIntegers K)} →
      (∀ φ : K →+* ℝ, 0 < φ ((a : K))) →
      ∀ (s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
        (e : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ)
        (σ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Gal(L/K)),
        (∀ p ∈ s, (m : NumberField.RingOfIntegers K) ∉ p.asIdeal) →
        Ideal.span {a} = ∏ p ∈ s, p.asIdeal ^ e p →
        (∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (L := L) p (σ p)) →
        (s.toList.map (fun p => σ p ^ e p)).prod = 1)
    (a : NumberField.RingOfIntegers K)
    (ha : a - 1 ∈ Ideal.span {(m : NumberField.RingOfIntegers K)})
    (hpos : ∀ φ : K →+* ℝ, 0 < φ ((a : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (a : K)) = 1 := by
  classical
  by_cases ha0 : a = 0
  · -- degenerate case: `a = 0`, hence the fractional ideal is `0`
    rw [ha0]
    have hz : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((0 : 𝓞 K) : K) = 0 :=
      FractionalIdeal.spanSingleton_eq_zero_iff.mpr (by simp)
    rw [hz]
    exact artinSym_zero hcomm
  · exact artinSym_spanSingleton_integral hcomm m hm hram hprinc a ha0 ha hpos

end NK.CFTLib.Arl
