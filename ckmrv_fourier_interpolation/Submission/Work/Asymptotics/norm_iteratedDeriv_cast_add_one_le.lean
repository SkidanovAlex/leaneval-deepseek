import Mathlib
import Submission.Work.Asymptotics.highPartDefs

namespace Work.Asymptotics

/-- The norm of a real number viewed in `ℂ` is its absolute value. -/
private lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

/-- The derivative of `t ↦ (t : ℂ) + 1` is the constant function `1`. -/
private lemma deriv_cast_add_one :
    deriv (fun t : ℝ => (t : ℂ) + 1) = fun _ => (1 : ℂ) := by
  funext y
  have h : HasDerivAt (fun t : ℝ => (t : ℂ) + 1) 1 y := by
    simpa using
      ((ContinuousLinearMap.hasDerivAt Complex.ofRealCLM (x := y)).add_const (1 : ℂ))
  exact h.deriv

/-- The iterated derivatives of `t ↦ (t : ℂ) + 1` of order at least two vanish. -/
private lemma iteratedDeriv_cast_add_one_add_two (n : ℕ) :
    iteratedDeriv (n + 2) (fun t : ℝ => (t : ℂ) + 1) = fun _ => (0 : ℂ) := by
  funext x
  rw [iteratedDeriv_succ', deriv_cast_add_one]
  rw [iteratedDeriv_succ']
  rw [show deriv (fun _ : ℝ => (1 : ℂ)) = (fun _ => (0 : ℂ)) from by
    funext z; exact deriv_const z (1 : ℂ)]
  simp

/-- The iterated derivatives of the linear function `t ↦ t + 1` (from `ℝ` to `ℂ`)
grow at most like `1 + |x|`, uniformly in the order of differentiation. -/
theorem norm_iteratedDeriv_cast_add_one_le (i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i (fun t : ℝ => (t : ℂ) + 1) x‖ ≤ 1 + |x| := by
  rcases i with _ | _ | n
  · rw [iteratedDeriv_zero]
    show ‖((x : ℂ) + 1)‖ ≤ 1 + |x|
    have hx : (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add]
    rw [hx, norm_ofReal_eq_abs]
    have h := abs_add_le x 1
    rw [abs_one] at h
    linarith
  · rw [iteratedDeriv_one, deriv_cast_add_one]
    simp
  · rw [iteratedDeriv_cast_add_one_add_two]
    simp
    linarith [abs_nonneg x]

end Work.Asymptotics
