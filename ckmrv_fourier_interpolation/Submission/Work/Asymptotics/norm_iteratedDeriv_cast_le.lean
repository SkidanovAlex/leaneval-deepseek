import Mathlib
import Submission.Work.Asymptotics.highPartDefs

namespace Work.Asymptotics

/-- The derivative of the real-to-complex inclusion `t ↦ (t : ℂ)` is the constant
function `1`. -/
private lemma deriv_ofReal_cast : deriv (fun t : ℝ => (t : ℂ)) = fun _ => (1 : ℂ) := by
  funext y
  rw [show (fun t : ℝ => (t : ℂ)) = ⇑Complex.ofRealCLM from rfl]
  rw [(Complex.ofRealCLM.hasDerivAt (x := y)).deriv]
  simp

theorem norm_iteratedDeriv_cast_le (i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i (fun t : ℝ => (t : ℂ)) x‖ ≤ 1 + |x| := by
  rcases i with _ | _ | j
  · rw [iteratedDeriv_zero, Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_nonneg x]
  · rw [iteratedDeriv_one, congrFun deriv_ofReal_cast x]
    simp only [norm_one]
    linarith [abs_nonneg x]
  · rw [iteratedDeriv_succ', deriv_ofReal_cast, iteratedDeriv_succ']
    rw [show deriv (fun _ : ℝ => (1 : ℂ)) = fun _ => (0 : ℂ) from
      funext (fun y => deriv_const y (1 : ℂ))]
    rw [iteratedDeriv_fun_const_zero]
    simp only [norm_zero]
    linarith [abs_nonneg x]

end Work.Asymptotics
