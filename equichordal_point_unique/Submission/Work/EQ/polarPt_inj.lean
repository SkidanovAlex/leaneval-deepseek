import Mathlib
import Submission.Work.EQ.Defs

namespace Work.EQ

/-- `polarPt c · ·` is injective on positive radii and angles in `(0, π)`: an equality of the
two polar representations forces both the radius and the angle to agree.  (The interval
restriction on the angle is what rules out the `2π` ambiguity of the polar representation.) -/
theorem polarPt_inj {c r r' θ θ' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (hθ : 0 < θ) (hθπ : θ < Real.pi) (hθ' : 0 < θ') (hθ'π : θ' < Real.pi)
    (h : polarPt c r θ = polarPt c r' θ') : r = r' ∧ θ = θ' := by
  -- cancel the common centre `c` and the common point `c` of the two representations
  have h1 : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
      = (r' : ℂ) * Complex.exp ((θ' : ℂ) * Complex.I) := by
    simpa only [polarPt] using add_left_cancel h
  -- radii: compare norms, using `‖exp (θ I)‖ = 1` and positivity of `r`, `r'`
  have hr_eq : r = r' := by
    have hn := congrArg norm h1
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] at hn
    have h' : |r| = |r'| := by simpa using hn
    rwa [abs_of_pos hr, abs_of_pos hr'] at h'
  subst hr_eq
  -- angles: cancel the (nonzero) radius and read off the real parts
  have hc : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have he : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((θ' : ℂ) * Complex.I) :=
    mul_left_cancel₀ hc h1
  have hcos : Real.cos θ = Real.cos θ' := by
    have := congrArg Complex.re he
    simpa [Complex.exp_ofReal_mul_I_re] using this
  -- cosine is injective on `[0, π]`, which contains both angles
  exact ⟨rfl, Real.strictAntiOn_cos.injOn (by simp [hθ.le, hθπ.le])
    (by simp [hθ'.le, hθ'π.le]) hcos⟩

end Work.EQ
