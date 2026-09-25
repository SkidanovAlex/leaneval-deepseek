import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq

/-!
# Extending a finite place of a number field to an algebraic extension

Let `K` be a number field, `K'` a field with an algebraic `K`-algebra structure, and `p` a finite
place of `K`, i.e. a height one prime of the ring of integers `𝓞 K`.  Then there is a valuation
subring `A` of `K'` whose restriction to `K` is exactly the valuation ring `𝒪_𝔭` of `K` at `p`.

This is the "extension of a place" statement used to speak about the places of an arbitrary
algebraic extension of a number field: every prime of `𝓞 K` has at least one place of `K'` above
it.

The content is the general fact (a form of Chevalley's theorem) that every valuation subring of a
field extends to any field extension, which is already available in the shared commons as
`Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq`.  We simply apply it to the
valuation ring `𝒪_𝔭` of `p`.
-/

namespace Commons.NumberTheory.NumberField.Valuation

theorem exists_valuationSubring_at_prime {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [Algebra.IsAlgebraic K K']
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ A : ValuationSubring K',
      A.comap (algebraMap K K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p :=
  Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)

end Commons.NumberTheory.NumberField.Valuation