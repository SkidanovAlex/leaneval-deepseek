import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Submission.Commons.NumberTheory.NumberField.ideal_valuation_rat_pow_of_liesOver

open scoped NumberField
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

theorem withVal_algebraMap_uniformContinuous
    {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)]
    (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hV : V.asIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v.asIdeal = Ideal.span ({(p : ℤ)} : Set ℤ)) :
    UniformContinuous
      (fun x : WithVal (v.valuation ℚ) =>
        WithVal.toVal (V.valuation K) (algebraMap ℚ K (WithVal.ofVal x))) := by
  have hV' : V.asIdeal.LiesOver v.asIdeal := by
    rw [hv]
    exact hV
  haveI : V.asIdeal.LiesOver v.asIdeal := hV'
  have hfunc : (fun x : WithVal (v.valuation ℚ) =>
        WithVal.toVal (V.valuation K) (algebraMap ℚ K (WithVal.ofVal x))) =
      (algebraMap (WithVal (v.valuation ℚ)) (WithVal (V.valuation K))) := by
    funext x
    rfl
  rw [hfunc]
  exact IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
    (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K) v V

end Commons.NumberTheory.NumberField