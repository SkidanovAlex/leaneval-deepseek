import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission.Sec3H

example (c : ℂ) : ContDiff ℝ 4 (fun x : ℝ => Complex.exp (c * (x : ℂ))) := by
  let L : ℝ →L[ℝ] ℂ := ((ContinuousLinearMap.mul ℝ ℂ) c).comp Complex.ofRealCLM
  have hL : ContDiff ℝ 4 (L : ℝ → ℂ) := ContinuousLinearMap.contDiff L
  have hexp : ContDiff ℝ 4 (Complex.exp : ℂ → ℂ) :=
    (Complex.contDiff_exp : ContDiff ℂ 4 (Complex.exp : ℂ → ℂ)).restrict_scalars ℝ
  have h : ContDiff ℝ 4 (fun x : ℝ => Complex.exp (L x)) := by
    change ContDiff ℝ 4 (Complex.exp ∘ (L : ℝ → ℂ))
    exact hexp.comp hL
  convert h using 1
  ext x
  exact congrArg Complex.exp (by simp [L, ContinuousLinearMap.mul_apply'])

example : ContDiff ℝ 4 (fun x : ℝ => Sec3.eθ x) := by
  have h : ContDiff ℝ 4 (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) := by
    exact (by
      let L : ℝ →L[ℝ] ℂ := ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp Complex.ofRealCLM
      have hL : ContDiff ℝ 4 (L : ℝ → ℂ) := ContinuousLinearMap.contDiff L
      have hexp : ContDiff ℝ 4 (Complex.exp : ℂ → ℂ) :=
        (Complex.contDiff_exp : ContDiff ℂ 4 (Complex.exp : ℂ → ℂ)).restrict_scalars ℝ
      have h1 : ContDiff ℝ 4 (fun x : ℝ => Complex.exp (L x)) := by
        change ContDiff ℝ 4 (Complex.exp ∘ (L : ℝ → ℂ))
        exact hexp.comp hL
      convert h1 using 1
      ext x
      exact congrArg Complex.exp (by simp [L, ContinuousLinearMap.mul_apply']))
  unfold Sec3.eθ
  convert h using 1
  ext x
  ring

end Submission.Sec3H
