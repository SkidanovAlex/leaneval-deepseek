import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip

namespace Work.LinnikAreas.OtherCharRepel

/-- A `zeroMult`-zero of a non-principal character lies in the open critical strip and therefore
has `λ(u) = (1 - Re u) log q > 0` for `2 ≤ q`.

`zeroMult χ u ≠ 0` says that `u` is a zero of the completed L-function of the *primitive*
character `χ.primitiveCharacter`, which is primitive and non-trivial; the classical
"zeros in the critical strip" theorem (`Commons.NumberTheory.Linnik.completedL_zero_strip`)
then gives `0 < Re u < 1`. -/
theorem zeroMultStripPos {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} {u : ℂ}
    (hχ : χ ≠ 1) (hz : Work.LinnikContract.zeroMult χ u ≠ 0) :
    0 < u.re ∧ u.re < 1 ∧ 0 < Work.LinnikContract.lamOf q u := by
  -- the primitive character inducing `χ` is primitive and non-trivial
  have hprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hne1 : χ.primitiveCharacter ≠ 1 := by
    intro h1
    refine hχ ?_
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  -- `u` is a zero of the completed L-function of the primitive character
  have hz' : @DirichletCharacter.completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩
      χ.primitiveCharacter u = 0 := by
    apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
    exact hz
  have hstrip : 0 < u.re ∧ u.re < 1 :=
    @Commons.NumberTheory.Linnik.completedL_zero_strip χ.conductor ⟨χ.conductor_ne_zero⟩
      χ.primitiveCharacter hne1 hprim u hz'
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  refine ⟨hstrip.1, hstrip.2, ?_⟩
  rw [Work.LinnikContract.lamOf]
  exact mul_pos (by linarith [hstrip.2]) hlog

end Work.LinnikAreas.OtherCharRepel
