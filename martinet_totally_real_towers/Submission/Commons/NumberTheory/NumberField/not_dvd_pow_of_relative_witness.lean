import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.NumberField.Basic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField

namespace Commons.NumberTheory.NumberField

/-
# `not_dvd_pow_of_relative_witness`

Relative (base-field) version of the trace-witness half of Dedekind's different theorem.

Let `F ⊆ L` be an extension of number fields, `P` a maximal ideal of `𝓞 L` with relative
ramification index `e := P.ramificationIdx (𝓞 F)` over the prime `p := P.under (𝓞 F)` of `𝓞 F`,
and suppose `p 𝓞 L = P ^ e · Q` with `P` and `Q` comaximal.  If `y ∈ Q` has relative integer
trace `Tr_{L/F}(y) ∉ p`, then `P ^ e` does **not** divide the relative different ideal
`differentIdeal (𝓞 F) (𝓞 L)`.

This is exactly Mathlib's `not_dvd_differentIdeal_of_intTrace_not_mem` applied to the ideal
`P ^ e` (which satisfies `P ^ e · Q = p 𝓞 L`), after endowing the fraction fields of the two
rings of integers with the (non-instance) `FractionRing.liftAlgebra` structure so that the
separability hypothesis `Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 L))`
is available.
-/
theorem not_dvd_pow_of_relative_witness
    {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L]
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsMaximal]
    {Q : Ideal (NumberField.RingOfIntegers L)} (hsup : P ⊔ Q = ⊤)
    (hspl : Ideal.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L))
        (P.under (NumberField.RingOfIntegers F)) =
      P ^ P.ramificationIdx (NumberField.RingOfIntegers F) * Q)
    (y : NumberField.RingOfIntegers L) (hyQ : y ∈ Q)
    (hy : Algebra.intTrace (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) y ∉
      P.under (NumberField.RingOfIntegers F)) :
    ¬ P ^ P.ramificationIdx (NumberField.RingOfIntegers F) ∣
      differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) := by
  letI : Algebra (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) :=
    FractionRing.liftAlgebra (𝓞 F) (FractionRing (𝓞 L))
  haveI : IsScalarTower (𝓞 F) (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) :=
    FractionRing.isScalarTower_liftAlgebra (𝓞 F) (FractionRing (𝓞 L))
  exact not_dvd_differentIdeal_of_intTrace_not_mem (𝓞 F)
    (P ^ P.ramificationIdx (𝓞 F)) Q hspl.symm y hyQ hy

end Commons.NumberTheory.NumberField