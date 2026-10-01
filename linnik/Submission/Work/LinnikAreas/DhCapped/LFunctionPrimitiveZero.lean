import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip

namespace Work.LinnikAreas.DhCapped

/-- If `u` is a zero of `L(s, χ)` in the sense of the Linnik contract (i.e. `zeroMult χ u ≠ 0`,
which counts the order of vanishing of the *completed* `L`-function of the primitive character
inducing `χ`), and `χ` is non-principal, then `u` is a genuine zero of the ordinary Dirichlet
`L`-function `L(s, χ.primitiveCharacter)` of the primitive character inducing `χ`.

Needed because the uniform zero-free regions are stated for the ordinary `L`-function of a
primitive character.  Route: `zeroMult χ u ≠ 0` gives
`completedLFunction χ.primitiveCharacter u = 0`
(`apply_eq_zero_of_analyticOrderNatAt_ne_zero`); `χ ≠ 1` gives `χ.primitiveCharacter ≠ 1`
(otherwise `changeLevel χ.conductor_dvd_level` of `1` would be `1 = χ`), so
`Commons.NumberTheory.Linnik.completedL_zero_strip` puts `u` in `0 < Re u < 1`
(`χ.primitiveCharacter` is primitive by `DirichletCharacter.primitiveCharacter_isPrimitive`);
then `Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip`
transfers the non-vanishing order, and `apply_eq_zero_of_analyticOrderNatAt_ne_zero` concludes.
The two `Commons` modules and `Mathlib` must be imported. -/
theorem LFunctionPrimitiveZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) {u : ℂ} (h : Work.LinnikContract.zeroMult χ u ≠ 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter u = 0 := by
  -- Unfold `zeroMult`: `h` says the completed L-function of the primitive character
  -- has non-zero vanishing order at `u`.
  have hmult : analyticOrderNatAt
      (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using h
  -- Hence `u` is a zero of that completed L-function.
  have hcomp : DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hmult
  -- The primitive character inducing a non-principal character is non-principal.
  have hχc : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    have h' : (DirichletCharacter.changeLevel χ.conductor_dvd_level) χ.primitiveCharacter =
        (DirichletCharacter.changeLevel χ.conductor_dvd_level)
          (1 : DirichletCharacter ℂ χ.conductor) := by
      rw [h1]
    rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_one]
      at h'
    exact h'
  -- It is primitive by construction.
  have hprim : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
  -- Zeros of the completed L-function of a primitive non-principal character lie in the strip.
  obtain ⟨hre0, hre1⟩ :=
    Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hχc hprim hcomp
  -- On the strip the ordinary and completed L-functions have the same vanishing order.
  have horder := Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
    χ.primitiveCharacter hχc hre0 hre1
  have hmultL : analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ 0 := by
    rw [horder]
    exact hmult
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hmultL

end Work.LinnikAreas.DhCapped
