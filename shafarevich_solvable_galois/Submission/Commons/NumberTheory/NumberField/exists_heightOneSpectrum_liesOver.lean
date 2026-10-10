import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

/-- Every nonzero prime of `𝓞 K` has a prime of `𝓞 L` lying over it, when `L / K` is a
finite extension of number fields.  Indeed `𝓞 L` is integral over `𝓞 K`, so the lying
over theorem for integral extensions applies. -/
theorem exists_heightOneSpectrum_liesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      P.asIdeal.LiesOver p.asIdeal := by
  obtain ⟨Q, hQmax, hQlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := _root_.NumberField.RingOfIntegers K)
      (S := _root_.NumberField.RingOfIntegers L) p.asIdeal
  exact ⟨⟨Q, hQmax.isPrime,
      Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q⟩, hQlies⟩

end Commons.NumberTheory.NumberField
