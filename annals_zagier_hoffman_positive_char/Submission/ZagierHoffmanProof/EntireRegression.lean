import Submission.ZagierHoffmanProof.EntireApp

/-!
# Regression tests for the entire/Tate series chapter

Concrete instances over `ZMod 2` of the results of `Entire.lean`, `EntireTwist.lean` and
`EntireApp.lean`.
-/

set_option autoImplicit false

open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

namespace EntireRegression

attribute [local instance 100] Classical.decEq

example : Entire (PowerSeries.X : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2))) :=
  Entire.X

example : Entire (PowerSeries.X ^ 5 : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2))) :=
  Entire.X_pow 5

example : SeriesBounded ((13 : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2)))) :=
  SeriesBounded.natCast 13

example : Entire (1 : PowerSeries (RatFunc.CompletionAtInfty (ZMod 3))) := Entire.one

/-- The `z`-coefficient of the Carlitz exponential over `K∞` (for `F = ZMod 2`) is `1`. -/
example : PowerSeries.coeff 1 (seriesToK (ZMod 2) (carlitzExp (ZMod 2))) = 1 := by
  rw [seriesToK_coeff, show PowerSeries.coeff 1 (carlitzExp (ZMod 2))
      = carlitzECoeff (ZMod 2) 1 from PowerSeries.coeff_mk _ _,
    show carlitzECoeff (ZMod 2) 1 = 1 by
      have := carlitzECoeff_pow (ZMod 2) 0
      simpa using this]
  exact map_one _

/-- The Carlitz exponential and logarithm over `K∞` are entire (instances). -/
example : Entire (seriesToK (ZMod 2) (carlitzExp (ZMod 2))) := entire_carlitzExp (ZMod 2)
example : Entire (seriesToK (ZMod 3) (carlitzLog (ZMod 3))) := entire_carlitzLog (ZMod 3)

/-- The exponent-`2` Frobenius twist of `z` is `z` itself. -/
example : frobTwist (R := ZMod 2) (p := 2) 1 (PowerSeries.X : PowerSeries (ZMod 2))
    = PowerSeries.X := by
  ext k
  rw [frobTwist_coeff, PowerSeries.coeff_X]
  by_cases h : k = 1
  · subst h; simp
  · simp [h]

/-- Entire series are closed under the Frobenius twist. -/
example (K : Type*) [Field K] [Valued K ℤᵐ⁰] {p : ℕ} [FrobPow K p] (n : ℕ) :
    Entire (frobTwist (R := K) (p := p) n (PowerSeries.X : PowerSeries K)) :=
  Entire.X.frobTwist n

end EntireRegression

end ZagierHoffmanPositiveChar
