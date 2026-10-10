import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

theorem liesOver_map_galRestrict {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [w.asIdeal.LiesOver p.asIdeal] (σ : L ≃ₐ[K] L) :
    (Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) w.asIdeal).LiesOver
      p.asIdeal := by
  exact Ideal.map_equiv_liesOver w.asIdeal p.asIdeal
    (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ)

end Commons.NumberTheory.NumberField