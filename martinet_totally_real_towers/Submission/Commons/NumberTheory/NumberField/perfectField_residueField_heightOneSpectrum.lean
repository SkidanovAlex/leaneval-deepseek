import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

/-- The residue field of a height-one prime of the ring of integers of a number field is a finite
field, hence perfect. -/
theorem perfectField_residueField_heightOneSpectrum {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    PerfectField p.asIdeal.ResidueField := by
  -- The ring of integers of a number field is a finite `ℤ`-module, hence has finite quotients;
  -- so the residue field at any nonzero prime is finite, and finite fields are perfect.
  haveI : Finite (NumberField.RingOfIntegers K ⧸ p.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  infer_instance

end Commons.NumberTheory.NumberField