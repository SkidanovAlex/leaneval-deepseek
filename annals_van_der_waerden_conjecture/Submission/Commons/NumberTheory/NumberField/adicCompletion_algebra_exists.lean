import Mathlib
import Submission.Commons.NumberTheory.NumberField.valuation_completion_algebraMap_exists

open scoped NumberField
open IsDedekindDomain
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

theorem adicCompletion_algebra_exists
    {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)]
    (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hV : V.asIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v.asIdeal = Ideal.span ({(p : ℤ)} : Set ℤ)) :
    Nonempty (Algebra (v.adicCompletion ℚ) (V.adicCompletion K)) := by
  obtain ⟨f⟩ := valuation_completion_algebraMap_exists p V hV v hv
  let φ : v.adicCompletion ℚ →+* V.adicCompletion K :=
    ((HeightOneSpectrum.adicCompletion.equiv (K := K) (v := V)).symm.toRingHom.comp f).comp
      (HeightOneSpectrum.adicCompletion.equiv (K := ℚ) (v := v)).toRingHom
  exact ⟨RingHom.toAlgebra φ⟩

end Commons.NumberTheory.NumberField
