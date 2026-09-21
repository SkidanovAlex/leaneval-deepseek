import Mathlib
import Submission.Work.OddCurveB.Est.Defs

namespace Work.OddCurveB.Est

/-!
# `Psi` is a two-sided inverse of `Phi`

`Phi n s` is the block-triangular map with rows
`[1,0,0,0]`, `[0,1,0,0]`, `[α,α,a,a]`, `[γ,-γ,c,-c]` (`α = pAA`, `a = pA`,
`γ = pGG`, `c = pC`), and `Psi n s` is the explicit candidate inverse.  Both are
`ContinuousLinearMap.pi` of `Fin 4`-families of rows, so it suffices to check the
two matrix identities coordinatewise; the diagonal `2×2` blocks invert because
`(2a)⁻¹ a = 1/2 = (2c)⁻¹ c` whenever `a = pA n s ≠ 0` and `c = pC n s ≠ 0`.
-/

theorem psi_inverse (n : ℕ) (s : ℝ) (hA : Work.OddCurveB.Est.pA n s ≠ 0)
    (hC : Work.OddCurveB.Est.pC n s ≠ 0) :
    Function.LeftInverse (fun w : Work.OddVolterra.St => Work.OddCurveB.Est.Psi n s w)
        (fun z : Work.OddVolterra.St => Work.OddCurveB.Est.Phi n s z) ∧
      Function.RightInverse (fun w : Work.OddVolterra.St => Work.OddCurveB.Est.Psi n s w)
        (fun z : Work.OddVolterra.St => Work.OddCurveB.Est.Phi n s z) := by
  constructor
  · intro z
    ext i
    fin_cases i
    all_goals simp [Phi, Psi, PhiRows, PsiRows, row2, row3, psiRow2, psiRow3, invU,
      invV, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Proj]
    all_goals field_simp
    all_goals ring
  · intro w
    ext i
    fin_cases i
    all_goals simp [Phi, Psi, PhiRows, PsiRows, row2, row3, psiRow2, psiRow3, invU,
      invV, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Proj]
    all_goals field_simp
    all_goals ring

end Work.OddCurveB.Est
