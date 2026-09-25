import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Field.Shrink
import Submission.Commons.Algebra.Module.small_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.completion_ringEquiv_of_algEquiv

open scoped NumberField

universe u

namespace Commons.NumberTheory.NumberField.Completion

/-- Every number field `K` admits a model in `Type 0` together with a ring isomorphism
`K ≃+* K₀`.  A number field is finite dimensional over `ℚ`, hence small, and `Shrink.{0} K`
carries the transported field structure. -/
theorem exists_shrink_field_ringEquiv (K : Type u) [Field K] [NumberField K] :
    ∃ (K₀ : Type) (_ : Field K₀), Nonempty (K ≃+* K₀) := by
  haveI : Small.{0} K := Commons.Algebra.Module.small_of_finiteDimensional (F := ℚ) (B := K)
  exact ⟨Shrink.{0} K, inferInstance, ⟨(Shrink.ringEquiv K).symm⟩⟩

theorem exists_adicCompletion_ringEquiv_type_zero
    (K : Type u) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀)
      (Q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₀)),
      Nonempty ((Q.adicCompletion K) ≃+* (Q₀.adicCompletion K₀)) := by
  obtain ⟨K₀, hK₀f, ⟨eKr⟩⟩ := exists_shrink_field_ringEquiv K
  letI : Field K₀ := hK₀f
  -- The canonical `ℚ`-algebra structure on `K₀`, through which `eKr` becomes `ℚ`-linear.
  haveI : CharZero K₀ :=
    CharZero.of_addMonoidHom (eKr : K →+* K₀).toAddMonoidHom (by simp) eKr.injective
  haveI : FiniteDimensional ℚ K₀ :=
    Module.Finite.of_surjective ((eKr.toRatAlgEquiv).toLinearEquiv.toLinearMap)
      (eKr.toRatAlgEquiv).toLinearEquiv.surjective
  haveI : NumberField K₀ := NumberField.mk
  -- Transport the finite place all the way to the completion.
  obtain ⟨Q₀, Φ, -⟩ :=
    Commons.NumberTheory.NumberField.completion_ringEquiv_of_algEquiv eKr.toRatAlgEquiv Q
  exact ⟨K₀, hK₀f, inferInstance, Q₀, ⟨Φ⟩⟩

end Commons.NumberTheory.NumberField.Completion