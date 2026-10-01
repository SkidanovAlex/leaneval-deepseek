import Mathlib
import Submission.Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero
import Submission.Work.LinnikContract.Defs

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.ZeroFreeTables.P9.prim

/-- Every non-trivial zero `u` of `L(s,χ)` (counted through the Linnik contract's `zeroMult`,
i.e. the vanishing order of the *completed* `L`-function of the primitive character inducing
`χ`) lies to the left of the line `Re s = 1`.

`zeroMult χ u ≠ 0` unfolds to `analyticOrderNatAt (Λ(·, χ.primitiveCharacter)) u ≠ 0`, so `u`
is a zero of the completed `L`-function of the primitive character `χ.primitiveCharacter`;
the latter is non-principal because `χ` is, and it is primitive by construction, so
`Commons.NumberTheory.Linnik.completedL_zero_strip` places `u` in the critical strip
`0 < Re u < 1`.  We only need the upper half `Re u < 1`. -/
theorem zeroMultReLtOne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {u : ℂ} (hu : Work.LinnikContract.zeroMult χ u ≠ 0) : u.re < 1 := by
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  -- `hu` unfolds to: the completed `L`-function of `χ.primitiveCharacter` has non-zero
  -- vanishing order at `u`, hence vanishes there.
  have hmult : analyticOrderNatAt
      (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using hu
  have hcomp : DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hmult
  -- The primitive character inducing a non-principal character is non-principal.
  have hχc : χ.primitiveCharacter ≠ 1 := by
    intro h1
    have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
    exact hχ h2.symm
  -- Zeros of the completed `L`-function of a primitive non-trivial character lie in the strip.
  exact (Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hχc
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) hcomp).2

end Work.ZeroFreeTables.P9.prim
