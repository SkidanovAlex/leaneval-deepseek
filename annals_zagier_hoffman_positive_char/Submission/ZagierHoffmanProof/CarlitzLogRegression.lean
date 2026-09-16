import Submission.ZagierHoffmanProof.CarlitzLog

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# Regression tests for the Carlitz logarithm

Concrete instances of `Submission.ZagierHoffmanProof.CarlitzLog` over `F₂ = ZMod 2` and
`F₃ = ZMod 3`: the first coefficients of `log_C`, the functional equation, and `log_C ∘ e_C = id`.
-/

namespace ZagierHoffmanPositiveChar

section Reg

open PowerSeries

attribute [local instance 100] Classical.decEq

example : (carlitzLog (ZMod 2)).coeff 1 = 1 := carlitzLog_coeff_one _
example : (carlitzLog (ZMod 2)).coeff 0 = 0 := carlitzLog_coeff_zero _
example : (carlitzLog (ZMod 2)).coeff (Nat.card (ZMod 2) ^ 1)
    = (((carlitzL (ZMod 2) 1 : (ZMod 2)[X]) : RatFunc (ZMod 2)))⁻¹ :=
  carlitzLog_coeff_pow (ZMod 2) 1
example : Nat.card (ZMod 2) ^ 1 = 2 := by rw [pow_one, Nat.card_eq_fintype_card, ZMod.card]
example : ((carlitzL (ZMod 2) 1 : (ZMod 2)[X])) = Polynomial.X - Polynomial.X ^ 2 := by
  rw [carlitzL]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- The functional equation of the Carlitz logarithm over `F₂`. -/
example : (carlitzLog (ZMod 2)).subst (carlitzSubst (ZMod 2))
    = PowerSeries.C (carlitzTheta (ZMod 2)) * carlitzLog (ZMod 2) :=
  carlitzLog_functional _

/-- ★ `log_C ∘ e_C = id` over `F₂`. -/
example : (carlitzLog (ZMod 2)).subst (carlitzExp (ZMod 2)) = PowerSeries.X :=
  carlitzLog_subst_exp _

/-- ★ `log_C ∘ e_C = id` over `F₃`. -/
example : (carlitzLog (ZMod 3)).subst (carlitzExp (ZMod 3)) = PowerSeries.X :=
  carlitzLog_subst_exp _

/-- `θ ^ n = θ` only for `n = 1`. -/
example : ¬ ((carlitzTheta (ZMod 3)) ^ 2 = carlitzTheta (ZMod 3)) := by
  intro h
  exact absurd ((carlitzTheta_pow_eq_iff (ZMod 3)).mp h) (by norm_num)

end Reg

end ZagierHoffmanPositiveChar
