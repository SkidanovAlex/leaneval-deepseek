import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

/-- The residue field at a nonzero prime ideal of the ring of integers of a number field
is finite: `𝓞 K` is a finite `ℤ`-module, hence has finite quotients.
(Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, XII.) -/
theorem finite_quotient_heightOneSpectrum {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Finite (NumberField.RingOfIntegers K ⧸ p.asIdeal) := by
  exact Ring.HasFiniteQuotients.finiteQuotient p.ne_bot

end Commons.NumberTheory.NumberField