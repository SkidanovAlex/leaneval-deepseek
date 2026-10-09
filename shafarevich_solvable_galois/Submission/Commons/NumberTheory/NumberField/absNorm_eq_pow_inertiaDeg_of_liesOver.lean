import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

/-- For a prime ideal `P` of `𝓞 L` lying over a prime ideal `p` of `𝓞 K` in a Galois (more
generally, any finite) extension of number fields `L/K`, the absolute norm of `P` is the
`f`-th power of the absolute norm of `p`, where `f` is the inertia degree (residue degree)
of `P` over `p`. -/
theorem absNorm_eq_pow_inertiaDeg_of_liesOver {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : P.asIdeal.LiesOver p.asIdeal) :
    Ideal.absNorm P.asIdeal =
      Ideal.absNorm p.asIdeal ^ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  rw [← Ideal.absNorm_pow_inertiaDeg (R := NumberField.RingOfIntegers K)
    (S := NumberField.RingOfIntegers L) p.asIdeal P.asIdeal]

end Commons.NumberTheory.NumberField