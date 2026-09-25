import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.QuasiFinite.Basic

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.NumberTheory.NumberField

open Algebra in
/-- Over a number field `L`, the ring of integers `𝓞 L` is a finite `ℤ`-module, hence
quasi-finite over `ℤ`; quasi-finiteness descends along the restriction of scalars
`ℤ → 𝓞 K`, so `𝓞 L` is quasi-finite over `𝓞 K`, and a quasi-finite algebra has only
finitely many primes over any ideal. -/
theorem finite_primesOver {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) : (Q.primesOver (NumberField.RingOfIntegers L)).Finite := by
  haveI : Module.Finite ℤ (NumberField.RingOfIntegers L) := inferInstance
  haveI : Algebra.QuasiFinite ℤ (NumberField.RingOfIntegers L) := inferInstance
  haveI : Algebra.QuasiFinite (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) :=
    Algebra.QuasiFinite.of_restrictScalars ℤ _ _
  exact Algebra.QuasiFinite.finite_primesOver Q

end Commons.NumberTheory.NumberField