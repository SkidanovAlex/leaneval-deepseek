import Mathlib
import Submission.Work.Asymptotics.highPartDefs

/-!
# `exp (-x)` is `ExpBdd 1 0`

The function `x ↦ exp (-x)` (real variable, complex values) is smooth and every iterated
derivative equals `(-1)^j · exp (-x)`, hence obeys the `ExpBdd 1 0` bound
`‖f^{(j)}(x)‖ ≤ C_j (1+|x|)^0 e^{-x}` with `C_j = 1`.
-/

namespace Work.Asymptotics

/-- The derivative of `x ↦ exp (-x)` on the real axis, viewed as a complex-valued function.

The computation is done on the real function `x ↦ Real.exp (-x)` and transported to `ℂ` with
`HasDerivAt.ofReal_comp`. -/
private lemma hasDerivAt_cexp_neg (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (-(y : ℂ))) (-Complex.exp (-(x : ℂ))) x := by
  have hreal : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    have h := (hasDerivAt_neg x).exp
    simpa using h
  have hcast : HasDerivAt (fun y : ℝ => ((Real.exp (-y) : ℝ) : ℂ))
      (((-Real.exp (-x)) : ℝ) : ℂ) x := hreal.ofReal_comp
  have hfun : (fun y : ℝ => ((Real.exp (-y) : ℝ) : ℂ))
      = (fun y : ℝ => Complex.exp (-(y : ℂ))) := by
    funext y
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  rw [hfun] at hcast
  simpa using hcast

/-- Every iterated derivative of `x ↦ exp (-x)` is `(-1)^j · exp (-x)`. -/
private lemma iteratedDeriv_cexp_neg (j : ℕ) :
    iteratedDeriv j (fun y : ℝ => Complex.exp (-(y : ℂ)))
      = fun x : ℝ => (-1 : ℂ) ^ j * Complex.exp (-(x : ℂ)) := by
  induction j with
  | zero => ext x; simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    ext x
    rw [((hasDerivAt_cexp_neg x).const_mul ((-1 : ℂ) ^ j)).deriv, pow_succ]
    ring

theorem ExpBdd_exp_neg :
    Work.Asymptotics.ExpBdd 1 0 (fun x : ℝ => Complex.exp (-(x : ℂ))) := by
  refine ⟨Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff (n := ⊤)).neg), fun j => ?_⟩
  refine ⟨1, zero_le_one, fun x => ?_⟩
  rw [iteratedDeriv_cexp_neg j]
  rw [norm_mul, Complex.norm_exp, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  simp

end Work.Asymptotics
