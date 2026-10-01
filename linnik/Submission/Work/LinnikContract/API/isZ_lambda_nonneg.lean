import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.API

/-- A zero in HB's working region has `λ(ρ) = (1 - Re ρ) log q ≥ 0`: it is a zero of the completed
L-function of a primitive non-trivial character, hence lies in the critical strip `0 < Re ρ < 1`
(`Commons…Linnik.completedL_zero_strip`, imported by `Pre`), and `2 ≤ q` makes `log q > 0`.

Prover notes: `zeroMult χ ρ ≠ 0` gives `completedLFunction χ.primitiveCharacter ρ = 0`
(`apply_eq_zero_of_analyticOrderNatAt_ne_zero`); non-principality of `χ.primitiveCharacter` follows
from `changeLevel_primitiveCharacter` + `changeLevel_one_iff`.  No `native_decide`. -/
theorem isZ_lambda_nonneg {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.LinnikContract.IsZ χ ρ) : 0 ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨hχ1, hzm, -⟩ := h
  -- `χ.primitiveCharacter` is primitive and non-trivial (it induces the non-trivial `χ`)
  have hprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hne1 : χ.primitiveCharacter ≠ 1 := by
    intro h1
    refine hχ1 ?_
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  -- `ρ` is a zero of the completed L-function of the primitive character
  have hz : @DirichletCharacter.completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩
      χ.primitiveCharacter ρ = 0 := by
    apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
    exact hzm
  -- hence it lies in the critical strip
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 :=
    @Commons.NumberTheory.Linnik.completedL_zero_strip χ.conductor ⟨χ.conductor_ne_zero⟩
      χ.primitiveCharacter hne1 hprim ρ hz
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  rw [Work.LinnikContract.lamOf]
  exact mul_nonneg (by linarith [hstrip.2]) (le_of_lt hlog)

end Work.LinnikContract.API
