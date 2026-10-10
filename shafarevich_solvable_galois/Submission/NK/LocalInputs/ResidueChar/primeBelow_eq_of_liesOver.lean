import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.LocalInputs.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalInputs.ResidueChar

/-- **The rational prime below `𝔮` is the prime `𝔮` lies over.** -/
theorem primeBelow_eq_of_liesOver {K : Type*} [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : 𝔮.asIdeal.LiesOver P.asIdeal) :
    NK.LocalInputs.primeBelow K 𝔮 = P := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NK.LocalInputs.primeBelow_asIdeal]
  exact h.over.symm

end NK.LocalInputs.ResidueChar
