import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.LocalInputs.Degree.sum_localDegree_eq_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.LocalInputs

/-- **The global degree is the sum of the local degrees, transported along a bijection of the
primes above a fixed rational prime.** -/
theorem finrank_eq_of_localDegree_eq {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (e : P.asIdeal.primesOver (NumberField.RingOfIntegers K₁) ≃
      P.asIdeal.primesOver (NumberField.RingOfIntegers K₂))
    (h : ∀ qq : P.asIdeal.primesOver (NumberField.RingOfIntegers K₁),
      localDegree K₁
          (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ (K := ℚ) (L := K₁) P qq) =
        localDegree K₂
          (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ (K := ℚ) (L := K₂) P
            (e qq))) :
    Module.finrank ℚ K₁ = Module.finrank ℚ K₂ := by
  rw [← Degree.sum_localDegree_eq_finrank K₁ P, ← Degree.sum_localDegree_eq_finrank K₂ P]
  rw [← Equiv.sum_comp e
    (fun qq => localDegree K₂
      (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ (K := ℚ) (L := K₂) P qq))]
  exact Finset.sum_congr rfl fun qq _ => h qq

end NK.LocalInputs
