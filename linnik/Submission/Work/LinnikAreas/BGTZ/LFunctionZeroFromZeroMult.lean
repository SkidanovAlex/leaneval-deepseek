import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroDensity.Montgomery.zeroMultBridge_proved

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter Complex

/-- For the principal character: a `zeroMult`-zero in the right half strip is a zero of `ζ`, hence
of `L(s,1)`. -/
theorem LFunction_one_eq_zero_of_zeroMult_one {q : ℕ} [NeZero q] {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (h : Work.LinnikContract.zeroMult (1 : DirichletCharacter ℂ q) ρ ≠ 0) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ = 0 := by
  have hcomp : completedRiemannZeta ρ = 0 := by
    rw [Work.LinnikAreas.boxMaxZeroAux.zeroMult_one_eq_completedRiemannZeta q ρ] at h
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h
  have hzeta : riemannZeta ρ = 0 := by
    rw [riemannZeta_def_of_ne_zero hρ0, hcomp, zero_div]
  have hρ1 : ρ ≠ 1 := by
    intro h1
    have := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one (1 : DirichletCharacter ℂ q) h
    rw [h1] at this; simp at this
  have hEP := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) (s := ρ) hρ1
  simp only [DirichletCharacter.LFunctionTrivChar] at hEP
  rw [hEP, hzeta, mul_zero]

/-- **The complex-`ρ` `zeroMult`/`L`-bridge for all characters** (the principal one included). -/
theorem LFunction_eq_zero_of_zeroMult_complex {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hre : (1 : ℝ) / 2 ≤ ρ.re) (hre1 : ρ.re ≤ 1)
    (hz : Work.LinnikContract.zeroMult χ ρ ≠ 0) :
    DirichletCharacter.LFunction χ ρ = 0 := by
  by_cases hχ : χ = 1
  · subst hχ
    refine LFunction_one_eq_zero_of_zeroMult_one ?_ hz
    intro h0
    rw [h0] at hre
    norm_num at hre
  · exact Work.ZeroDensity.Montgomery.zeroMultBridge_proved q χ ρ hχ hre hre1 hz

end Work.LinnikAreas.BGTZ
