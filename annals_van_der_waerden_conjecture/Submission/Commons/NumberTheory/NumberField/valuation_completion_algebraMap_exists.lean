import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Submission.Commons.NumberTheory.NumberField.ideal_valuation_rat_pow_of_liesOver
import Submission.Commons.NumberTheory.NumberField.withVal_algebraMap_uniformContinuous

open scoped NumberField
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

theorem valuation_completion_algebraMap_exists
    {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)]
    (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hV : V.asIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v.asIdeal = Ideal.span ({(p : ℤ)} : Set ℤ)) :
    Nonempty ((v.valuation ℚ).Completion →+* (V.valuation K).Completion) := by
  have hV' : V.asIdeal.LiesOver v.asIdeal := by
    rw [hv]
    exact hV
  haveI : V.asIdeal.LiesOver v.asIdeal := hV'
  have hu : UniformContinuous
      (algebraMap (WithVal (v.valuation ℚ)) (WithVal (V.valuation K))) :=
    IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
      (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K) v V
  have hf : Continuous (algebraMap (WithVal (v.valuation ℚ)) (WithVal (V.valuation K))) :=
    hu.continuous
  exact ⟨UniformSpace.Completion.mapRingHom (α := WithVal (v.valuation ℚ))
    (β := WithVal (V.valuation K))
    (algebraMap (WithVal (v.valuation ℚ)) (WithVal (V.valuation K))) hf⟩

end Commons.NumberTheory.NumberField